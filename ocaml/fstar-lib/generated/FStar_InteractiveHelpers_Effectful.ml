open Prims
let (term_eq :
  FStarC_Reflection_Types.term -> FStarC_Reflection_Types.term -> Prims.bool)
  = FStar_Reflection_TermEq_Simple.term_eq
type cast_info =
  {
  term: FStarC_Reflection_Types.term ;
  p_ty:
    FStar_InteractiveHelpers_ExploreTerm.type_info
      FStar_Pervasives_Native.option
    ;
  exp_ty:
    FStar_InteractiveHelpers_ExploreTerm.type_info
      FStar_Pervasives_Native.option
    }
let (__proj__Mkcast_info__item__term :
  cast_info -> FStarC_Reflection_Types.term) =
  fun projectee -> match projectee with | { term; p_ty; exp_ty;_} -> term
let (__proj__Mkcast_info__item__p_ty :
  cast_info ->
    FStar_InteractiveHelpers_ExploreTerm.type_info
      FStar_Pervasives_Native.option)
  = fun projectee -> match projectee with | { term; p_ty; exp_ty;_} -> p_ty
let (__proj__Mkcast_info__item__exp_ty :
  cast_info ->
    FStar_InteractiveHelpers_ExploreTerm.type_info
      FStar_Pervasives_Native.option)
  = fun projectee -> match projectee with | { term; p_ty; exp_ty;_} -> exp_ty
let (mk_cast_info :
  FStarC_Reflection_Types.term ->
    FStar_InteractiveHelpers_ExploreTerm.type_info
      FStar_Pervasives_Native.option ->
      FStar_InteractiveHelpers_ExploreTerm.type_info
        FStar_Pervasives_Native.option -> cast_info)
  = fun t -> fun p_ty -> fun exp_ty -> { term = t; p_ty; exp_ty }
let (cast_info_to_string :
  cast_info -> (Prims.string, unit) FStar_Tactics_Effect.tac_repr) =
  fun info ->
    let uu___ =
      let uu___1 = FStarC_Tactics_V1_Builtins.term_to_string info.term in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.InteractiveHelpers.Effectful.fst"
                 (Prims.of_int (33)) (Prims.of_int (20)) (Prims.of_int (33))
                 (Prims.of_int (44)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.InteractiveHelpers.Effectful.fst"
                 (Prims.of_int (33)) (Prims.of_int (20)) (Prims.of_int (35))
                 (Prims.of_int (56))))) (Obj.magic uu___1)
        (fun uu___2 ->
           (fun uu___2 ->
              let uu___3 =
                let uu___4 =
                  let uu___5 =
                    FStar_InteractiveHelpers_Base.option_to_string
                      FStar_InteractiveHelpers_ExploreTerm.type_info_to_string
                      info.p_ty in
                  FStar_Tactics_Effect.tac_bind
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range
                             "FStar.InteractiveHelpers.Effectful.fst"
                             (Prims.of_int (34)) (Prims.of_int (2))
                             (Prims.of_int (34)) (Prims.of_int (48)))))
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range
                             "FStar.InteractiveHelpers.Effectful.fst"
                             (Prims.of_int (34)) (Prims.of_int (2))
                             (Prims.of_int (35)) (Prims.of_int (56)))))
                    (Obj.magic uu___5)
                    (fun uu___6 ->
                       (fun uu___6 ->
                          let uu___7 =
                            let uu___8 =
                              let uu___9 =
                                FStar_InteractiveHelpers_Base.option_to_string
                                  FStar_InteractiveHelpers_ExploreTerm.type_info_to_string
                                  info.exp_ty in
                              FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.InteractiveHelpers.Effectful.fst"
                                         (Prims.of_int (35))
                                         (Prims.of_int (2))
                                         (Prims.of_int (35))
                                         (Prims.of_int (50)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range "Prims.fst"
                                         (Prims.of_int (611))
                                         (Prims.of_int (19))
                                         (Prims.of_int (611))
                                         (Prims.of_int (31)))))
                                (Obj.magic uu___9)
                                (fun uu___10 ->
                                   FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___11 -> Prims.strcat uu___10 ")")) in
                            FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "FStar.InteractiveHelpers.Effectful.fst"
                                       (Prims.of_int (35)) (Prims.of_int (2))
                                       (Prims.of_int (35))
                                       (Prims.of_int (56)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range "Prims.fst"
                                       (Prims.of_int (611))
                                       (Prims.of_int (19))
                                       (Prims.of_int (611))
                                       (Prims.of_int (31)))))
                              (Obj.magic uu___8)
                              (fun uu___9 ->
                                 FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___10 -> Prims.strcat ") (" uu___9)) in
                          Obj.magic
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "FStar.InteractiveHelpers.Effectful.fst"
                                        (Prims.of_int (34))
                                        (Prims.of_int (51))
                                        (Prims.of_int (35))
                                        (Prims.of_int (56)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range "Prims.fst"
                                        (Prims.of_int (611))
                                        (Prims.of_int (19))
                                        (Prims.of_int (611))
                                        (Prims.of_int (31)))))
                               (Obj.magic uu___7)
                               (fun uu___8 ->
                                  FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___9 -> Prims.strcat uu___6 uu___8))))
                         uu___6) in
                FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range
                           "FStar.InteractiveHelpers.Effectful.fst"
                           (Prims.of_int (34)) (Prims.of_int (2))
                           (Prims.of_int (35)) (Prims.of_int (56)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Prims.fst"
                           (Prims.of_int (611)) (Prims.of_int (19))
                           (Prims.of_int (611)) (Prims.of_int (31)))))
                  (Obj.magic uu___4)
                  (fun uu___5 ->
                     FStar_Tactics_Effect.lift_div_tac
                       (fun uu___6 -> Prims.strcat ") (" uu___5)) in
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.InteractiveHelpers.Effectful.fst"
                            (Prims.of_int (33)) (Prims.of_int (47))
                            (Prims.of_int (35)) (Prims.of_int (56)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Prims.fst"
                            (Prims.of_int (611)) (Prims.of_int (19))
                            (Prims.of_int (611)) (Prims.of_int (31)))))
                   (Obj.magic uu___3)
                   (fun uu___4 ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___5 -> Prims.strcat uu___2 uu___4)))) uu___2) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.InteractiveHelpers.Effectful.fst"
               (Prims.of_int (33)) (Prims.of_int (20)) (Prims.of_int (35))
               (Prims.of_int (56)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Prims.fst" (Prims.of_int (611))
               (Prims.of_int (19)) (Prims.of_int (611)) (Prims.of_int (31)))))
      (Obj.magic uu___)
      (fun uu___1 ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___2 -> Prims.strcat "Mkcast_info (" uu___1))
type effect_info =
  {
  ei_type: FStar_InteractiveHelpers_ExploreTerm.effect_type ;
  ei_ret_type: FStar_InteractiveHelpers_ExploreTerm.type_info ;
  ei_pre: FStarC_Reflection_Types.term FStar_Pervasives_Native.option ;
  ei_post: FStarC_Reflection_Types.term FStar_Pervasives_Native.option }
let (__proj__Mkeffect_info__item__ei_type :
  effect_info -> FStar_InteractiveHelpers_ExploreTerm.effect_type) =
  fun projectee ->
    match projectee with
    | { ei_type; ei_ret_type; ei_pre; ei_post;_} -> ei_type
let (__proj__Mkeffect_info__item__ei_ret_type :
  effect_info -> FStar_InteractiveHelpers_ExploreTerm.type_info) =
  fun projectee ->
    match projectee with
    | { ei_type; ei_ret_type; ei_pre; ei_post;_} -> ei_ret_type
let (__proj__Mkeffect_info__item__ei_pre :
  effect_info -> FStarC_Reflection_Types.term FStar_Pervasives_Native.option)
  =
  fun projectee ->
    match projectee with
    | { ei_type; ei_ret_type; ei_pre; ei_post;_} -> ei_pre
let (__proj__Mkeffect_info__item__ei_post :
  effect_info -> FStarC_Reflection_Types.term FStar_Pervasives_Native.option)
  =
  fun projectee ->
    match projectee with
    | { ei_type; ei_ret_type; ei_pre; ei_post;_} -> ei_post
let (mk_effect_info :
  FStar_InteractiveHelpers_ExploreTerm.effect_type ->
    FStar_InteractiveHelpers_ExploreTerm.type_info ->
      FStarC_Reflection_Types.term FStar_Pervasives_Native.option ->
        FStarC_Reflection_Types.term FStar_Pervasives_Native.option ->
          effect_info)
  =
  fun uu___ ->
    fun uu___1 ->
      fun uu___2 ->
        fun uu___3 ->
          {
            ei_type = uu___;
            ei_ret_type = uu___1;
            ei_pre = uu___2;
            ei_post = uu___3
          }
let (effect_info_to_string :
  effect_info -> (Prims.string, unit) FStar_Tactics_Effect.tac_repr) =
  fun c ->
    let uu___ =
      let uu___1 =
        let uu___2 =
          let uu___3 =
            FStar_InteractiveHelpers_Base.option_to_string
              FStarC_Tactics_V1_Builtins.term_to_string c.ei_pre in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range
                     "FStar.InteractiveHelpers.Effectful.fst"
                     (Prims.of_int (52)) (Prims.of_int (2))
                     (Prims.of_int (52)) (Prims.of_int (42)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range
                     "FStar.InteractiveHelpers.Effectful.fst"
                     (Prims.of_int (52)) (Prims.of_int (2))
                     (Prims.of_int (54)) (Prims.of_int (49)))))
            (Obj.magic uu___3)
            (fun uu___4 ->
               (fun uu___4 ->
                  let uu___5 =
                    let uu___6 =
                      let uu___7 =
                        FStar_InteractiveHelpers_ExploreTerm.type_info_to_string
                          c.ei_ret_type in
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.InteractiveHelpers.Effectful.fst"
                                 (Prims.of_int (53)) (Prims.of_int (2))
                                 (Prims.of_int (53)) (Prims.of_int (35)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.InteractiveHelpers.Effectful.fst"
                                 (Prims.of_int (53)) (Prims.of_int (2))
                                 (Prims.of_int (54)) (Prims.of_int (49)))))
                        (Obj.magic uu___7)
                        (fun uu___8 ->
                           (fun uu___8 ->
                              let uu___9 =
                                let uu___10 =
                                  let uu___11 =
                                    FStar_InteractiveHelpers_Base.option_to_string
                                      FStarC_Tactics_V1_Builtins.term_to_string
                                      c.ei_post in
                                  FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.InteractiveHelpers.Effectful.fst"
                                             (Prims.of_int (54))
                                             (Prims.of_int (2))
                                             (Prims.of_int (54))
                                             (Prims.of_int (43)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range "Prims.fst"
                                             (Prims.of_int (611))
                                             (Prims.of_int (19))
                                             (Prims.of_int (611))
                                             (Prims.of_int (31)))))
                                    (Obj.magic uu___11)
                                    (fun uu___12 ->
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___13 ->
                                            Prims.strcat uu___12 ")")) in
                                FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "FStar.InteractiveHelpers.Effectful.fst"
                                           (Prims.of_int (54))
                                           (Prims.of_int (2))
                                           (Prims.of_int (54))
                                           (Prims.of_int (49)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range "Prims.fst"
                                           (Prims.of_int (611))
                                           (Prims.of_int (19))
                                           (Prims.of_int (611))
                                           (Prims.of_int (31)))))
                                  (Obj.magic uu___10)
                                  (fun uu___11 ->
                                     FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___12 ->
                                          Prims.strcat ") (" uu___11)) in
                              Obj.magic
                                (FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "FStar.InteractiveHelpers.Effectful.fst"
                                            (Prims.of_int (53))
                                            (Prims.of_int (38))
                                            (Prims.of_int (54))
                                            (Prims.of_int (49)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range "Prims.fst"
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
                            (FStar_Range.mk_range
                               "FStar.InteractiveHelpers.Effectful.fst"
                               (Prims.of_int (53)) (Prims.of_int (2))
                               (Prims.of_int (54)) (Prims.of_int (49)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Prims.fst"
                               (Prims.of_int (611)) (Prims.of_int (19))
                               (Prims.of_int (611)) (Prims.of_int (31)))))
                      (Obj.magic uu___6)
                      (fun uu___7 ->
                         FStar_Tactics_Effect.lift_div_tac
                           (fun uu___8 -> Prims.strcat ") (" uu___7)) in
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.InteractiveHelpers.Effectful.fst"
                                (Prims.of_int (52)) (Prims.of_int (45))
                                (Prims.of_int (54)) (Prims.of_int (49)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Prims.fst"
                                (Prims.of_int (611)) (Prims.of_int (19))
                                (Prims.of_int (611)) (Prims.of_int (31)))))
                       (Obj.magic uu___5)
                       (fun uu___6 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___7 -> Prims.strcat uu___4 uu___6))))
                 uu___4) in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range
                   "FStar.InteractiveHelpers.Effectful.fst"
                   (Prims.of_int (52)) (Prims.of_int (2)) (Prims.of_int (54))
                   (Prims.of_int (49)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Prims.fst" (Prims.of_int (611))
                   (Prims.of_int (19)) (Prims.of_int (611))
                   (Prims.of_int (31))))) (Obj.magic uu___2)
          (fun uu___3 ->
             FStar_Tactics_Effect.lift_div_tac
               (fun uu___4 -> Prims.strcat " (" uu___3)) in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.InteractiveHelpers.Effectful.fst"
                 (Prims.of_int (51)) (Prims.of_int (36)) (Prims.of_int (54))
                 (Prims.of_int (49)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Prims.fst" (Prims.of_int (611))
                 (Prims.of_int (19)) (Prims.of_int (611)) (Prims.of_int (31)))))
        (Obj.magic uu___1)
        (fun uu___2 ->
           FStar_Tactics_Effect.lift_div_tac
             (fun uu___3 ->
                Prims.strcat
                  (FStar_InteractiveHelpers_ExploreTerm.effect_type_to_string
                     c.ei_type) uu___2)) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.InteractiveHelpers.Effectful.fst"
               (Prims.of_int (51)) (Prims.of_int (2)) (Prims.of_int (54))
               (Prims.of_int (49)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Prims.fst" (Prims.of_int (611))
               (Prims.of_int (19)) (Prims.of_int (611)) (Prims.of_int (31)))))
      (Obj.magic uu___)
      (fun uu___1 ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___2 -> Prims.strcat "Mkeffect_info " uu___1))
type eterm_info =
  {
  einfo: effect_info ;
  head: FStarC_Reflection_Types.term ;
  parameters: cast_info Prims.list }
let (__proj__Mketerm_info__item__einfo : eterm_info -> effect_info) =
  fun projectee ->
    match projectee with | { einfo; head; parameters;_} -> einfo
let (__proj__Mketerm_info__item__head :
  eterm_info -> FStarC_Reflection_Types.term) =
  fun projectee ->
    match projectee with | { einfo; head; parameters;_} -> head
let (__proj__Mketerm_info__item__parameters :
  eterm_info -> cast_info Prims.list) =
  fun projectee ->
    match projectee with | { einfo; head; parameters;_} -> parameters
let (eterm_info_to_string :
  eterm_info -> (Prims.string, unit) FStar_Tactics_Effect.tac_repr) =
  fun info ->
    let uu___ =
      FStar_Tactics_Util.map
        (fun x ->
           let uu___1 =
             let uu___2 = cast_info_to_string x in
             FStar_Tactics_Effect.tac_bind
               (FStar_Sealed.seal
                  (Obj.magic
                     (FStar_Range.mk_range
                        "FStar.InteractiveHelpers.Effectful.fst"
                        (Prims.of_int (66)) (Prims.of_int (35))
                        (Prims.of_int (66)) (Prims.of_int (56)))))
               (FStar_Sealed.seal
                  (Obj.magic
                     (FStar_Range.mk_range "Prims.fst" (Prims.of_int (611))
                        (Prims.of_int (19)) (Prims.of_int (611))
                        (Prims.of_int (31))))) (Obj.magic uu___2)
               (fun uu___3 ->
                  FStar_Tactics_Effect.lift_div_tac
                    (fun uu___4 -> Prims.strcat uu___3 ");  \n")) in
           FStar_Tactics_Effect.tac_bind
             (FStar_Sealed.seal
                (Obj.magic
                   (FStar_Range.mk_range
                      "FStar.InteractiveHelpers.Effectful.fst"
                      (Prims.of_int (66)) (Prims.of_int (35))
                      (Prims.of_int (66)) (Prims.of_int (67)))))
             (FStar_Sealed.seal
                (Obj.magic
                   (FStar_Range.mk_range "Prims.fst" (Prims.of_int (611))
                      (Prims.of_int (19)) (Prims.of_int (611))
                      (Prims.of_int (31))))) (Obj.magic uu___1)
             (fun uu___2 ->
                FStar_Tactics_Effect.lift_div_tac
                  (fun uu___3 -> Prims.strcat "(" uu___2))) info.parameters in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.InteractiveHelpers.Effectful.fst"
               (Prims.of_int (66)) (Prims.of_int (15)) (Prims.of_int (66))
               (Prims.of_int (84)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.InteractiveHelpers.Effectful.fst"
               (Prims.of_int (66)) (Prims.of_int (87)) (Prims.of_int (71))
               (Prims.of_int (18))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun params ->
            let uu___1 =
              Obj.magic
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___2 ->
                      FStar_List_Tot_Base.fold_left
                        (fun x -> fun y -> Prims.strcat x y) "" params)) in
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range
                          "FStar.InteractiveHelpers.Effectful.fst"
                          (Prims.of_int (67)) (Prims.of_int (19))
                          (Prims.of_int (67)) (Prims.of_int (66)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range
                          "FStar.InteractiveHelpers.Effectful.fst"
                          (Prims.of_int (68)) (Prims.of_int (2))
                          (Prims.of_int (71)) (Prims.of_int (18)))))
                 (Obj.magic uu___1)
                 (fun uu___2 ->
                    (fun params_str ->
                       let uu___2 =
                         let uu___3 = effect_info_to_string info.einfo in
                         FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "FStar.InteractiveHelpers.Effectful.fst"
                                    (Prims.of_int (69)) (Prims.of_int (2))
                                    (Prims.of_int (69)) (Prims.of_int (34)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "FStar.InteractiveHelpers.Effectful.fst"
                                    (Prims.of_int (69)) (Prims.of_int (2))
                                    (Prims.of_int (71)) (Prims.of_int (18)))))
                           (Obj.magic uu___3)
                           (fun uu___4 ->
                              (fun uu___4 ->
                                 let uu___5 =
                                   let uu___6 =
                                     let uu___7 =
                                       FStarC_Tactics_V1_Builtins.term_to_string
                                         info.head in
                                     FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.InteractiveHelpers.Effectful.fst"
                                                (Prims.of_int (70))
                                                (Prims.of_int (2))
                                                (Prims.of_int (70))
                                                (Prims.of_int (26)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Prims.fst"
                                                (Prims.of_int (611))
                                                (Prims.of_int (19))
                                                (Prims.of_int (611))
                                                (Prims.of_int (31)))))
                                       (Obj.magic uu___7)
                                       (fun uu___8 ->
                                          FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___9 ->
                                               Prims.strcat uu___8
                                                 (Prims.strcat ")\n["
                                                    (Prims.strcat params_str
                                                       "]")))) in
                                   FStar_Tactics_Effect.tac_bind
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "FStar.InteractiveHelpers.Effectful.fst"
                                              (Prims.of_int (70))
                                              (Prims.of_int (2))
                                              (Prims.of_int (71))
                                              (Prims.of_int (18)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range "Prims.fst"
                                              (Prims.of_int (611))
                                              (Prims.of_int (19))
                                              (Prims.of_int (611))
                                              (Prims.of_int (31)))))
                                     (Obj.magic uu___6)
                                     (fun uu___7 ->
                                        FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___8 ->
                                             Prims.strcat ") (" uu___7)) in
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "FStar.InteractiveHelpers.Effectful.fst"
                                               (Prims.of_int (69))
                                               (Prims.of_int (37))
                                               (Prims.of_int (71))
                                               (Prims.of_int (18)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range "Prims.fst"
                                               (Prims.of_int (611))
                                               (Prims.of_int (19))
                                               (Prims.of_int (611))
                                               (Prims.of_int (31)))))
                                      (Obj.magic uu___5)
                                      (fun uu___6 ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___7 ->
                                              Prims.strcat uu___4 uu___6))))
                                uu___4) in
                       Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.InteractiveHelpers.Effectful.fst"
                                     (Prims.of_int (69)) (Prims.of_int (2))
                                     (Prims.of_int (71)) (Prims.of_int (18)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range "Prims.fst"
                                     (Prims.of_int (611)) (Prims.of_int (19))
                                     (Prims.of_int (611)) (Prims.of_int (31)))))
                            (Obj.magic uu___2)
                            (fun uu___3 ->
                               FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___4 ->
                                    Prims.strcat "Mketerm_info (" uu___3))))
                      uu___2))) uu___1)
let (mk_eterm_info :
  effect_info ->
    FStarC_Reflection_Types.term -> cast_info Prims.list -> eterm_info)
  =
  fun uu___ ->
    fun uu___1 ->
      fun uu___2 -> { einfo = uu___; head = uu___1; parameters = uu___2 }
let rec (decompose_application_aux :
  FStarC_Reflection_Types.env ->
    FStarC_Reflection_Types.term ->
      ((FStarC_Reflection_Types.term * cast_info Prims.list), unit)
        FStar_Tactics_Effect.tac_repr)
  =
  fun e ->
    fun t ->
      let uu___ = FStarC_Tactics_V1_Builtins.inspect t in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.InteractiveHelpers.Effectful.fst"
                 (Prims.of_int (83)) (Prims.of_int (8)) (Prims.of_int (83))
                 (Prims.of_int (17)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.InteractiveHelpers.Effectful.fst"
                 (Prims.of_int (83)) (Prims.of_int (2)) (Prims.of_int (101))
                 (Prims.of_int (14))))) (Obj.magic uu___)
        (fun uu___1 ->
           (fun uu___1 ->
              match uu___1 with
              | FStarC_Reflection_V1_Data.Tv_App (hd, (a, qualif)) ->
                  Obj.magic
                    (Obj.repr
                       (let uu___2 = decompose_application_aux e hd in
                        FStar_Tactics_Effect.tac_bind
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "FStar.InteractiveHelpers.Effectful.fst"
                                   (Prims.of_int (85)) (Prims.of_int (22))
                                   (Prims.of_int (85)) (Prims.of_int (52)))))
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "FStar.InteractiveHelpers.Effectful.fst"
                                   (Prims.of_int (84)) (Prims.of_int (28))
                                   (Prims.of_int (100)) (Prims.of_int (28)))))
                          (Obj.magic uu___2)
                          (fun uu___3 ->
                             (fun uu___3 ->
                                match uu___3 with
                                | (hd0, params) ->
                                    let uu___4 =
                                      FStar_InteractiveHelpers_ExploreTerm.get_type_info
                                        e a in
                                    Obj.magic
                                      (FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "FStar.InteractiveHelpers.Effectful.fst"
                                                  (Prims.of_int (87))
                                                  (Prims.of_int (17))
                                                  (Prims.of_int (87))
                                                  (Prims.of_int (34)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "FStar.InteractiveHelpers.Effectful.fst"
                                                  (Prims.of_int (87))
                                                  (Prims.of_int (37))
                                                  (Prims.of_int (100))
                                                  (Prims.of_int (28)))))
                                         (Obj.magic uu___4)
                                         (fun uu___5 ->
                                            (fun a_type ->
                                               let uu___5 =
                                                 FStar_InteractiveHelpers_ExploreTerm.safe_tc
                                                   e hd in
                                               Obj.magic
                                                 (FStar_Tactics_Effect.tac_bind
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "FStar.InteractiveHelpers.Effectful.fst"
                                                             (Prims.of_int (89))
                                                             (Prims.of_int (16))
                                                             (Prims.of_int (89))
                                                             (Prims.of_int (28)))))
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "FStar.InteractiveHelpers.Effectful.fst"
                                                             (Prims.of_int (89))
                                                             (Prims.of_int (31))
                                                             (Prims.of_int (100))
                                                             (Prims.of_int (28)))))
                                                    (Obj.magic uu___5)
                                                    (fun uu___6 ->
                                                       (fun hd_ty ->
                                                          let uu___6 =
                                                            match hd_ty with
                                                            | FStar_Pervasives_Native.None
                                                                ->
                                                                Obj.magic
                                                                  (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Pervasives_Native.None)))
                                                            | FStar_Pervasives_Native.Some
                                                                hd_ty' ->
                                                                Obj.magic
                                                                  (Obj.repr
                                                                    (let uu___7
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.inspect
                                                                    hd_ty' in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (28)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (19)))))
                                                                    (Obj.magic
                                                                    uu___7)
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    match uu___8
                                                                    with
                                                                    | 
                                                                    FStarC_Reflection_V1_Data.Tv_Arrow
                                                                    (b, c) ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___9
                                                                    =
                                                                    let uu___10
                                                                    =
                                                                    FStar_Tactics_V1_Derived.binder_sort
                                                                    b in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (55)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (56)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_InteractiveHelpers_ExploreTerm.get_type_info_from_type
                                                                    uu___11))
                                                                    uu___11) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (56)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (56)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___10))))
                                                                    | 
                                                                    uu___9 ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Pervasives_Native.None))))
                                                                    uu___8))) in
                                                          Obj.magic
                                                            (FStar_Tactics_Effect.tac_bind
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (19)))))
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (100))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (100))
                                                                    (Prims.of_int (28)))))
                                                               (Obj.magic
                                                                  uu___6)
                                                               (fun
                                                                  param_type
                                                                  ->
                                                                  FStar_Tactics_Effect.lift_div_tac
                                                                    (
                                                                    fun
                                                                    uu___7 ->
                                                                    (hd0,
                                                                    ((mk_cast_info
                                                                    a a_type
                                                                    param_type)
                                                                    ::
                                                                    params))))))
                                                         uu___6))) uu___5)))
                               uu___3)))
              | uu___2 ->
                  Obj.magic
                    (Obj.repr
                       (FStar_Tactics_Effect.lift_div_tac
                          (fun uu___3 -> (t, []))))) uu___1)
let (decompose_application :
  FStarC_Reflection_Types.env ->
    FStarC_Reflection_Types.term ->
      ((FStarC_Reflection_Types.term * cast_info Prims.list), unit)
        FStar_Tactics_Effect.tac_repr)
  =
  fun e ->
    fun t ->
      let uu___ = decompose_application_aux e t in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.InteractiveHelpers.Effectful.fst"
                 (Prims.of_int (105)) (Prims.of_int (19))
                 (Prims.of_int (105)) (Prims.of_int (48)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.InteractiveHelpers.Effectful.fst"
                 (Prims.of_int (104)) (Prims.of_int (31))
                 (Prims.of_int (106)) (Prims.of_int (25)))))
        (Obj.magic uu___)
        (fun uu___1 ->
           FStar_Tactics_Effect.lift_div_tac
             (fun uu___2 ->
                match uu___1 with
                | (hd, params) -> (hd, (FStar_List_Tot_Base.rev params))))
let (comp_view_to_effect_info :
  Prims.bool ->
    FStarC_Reflection_V1_Data.comp_view ->
      (effect_info FStar_Pervasives_Native.option, unit)
        FStar_Tactics_Effect.tac_repr)
  =
  fun dbg ->
    fun cv ->
      match cv with
      | FStarC_Reflection_V1_Data.C_Total ret_ty ->
          let uu___ =
            FStar_InteractiveHelpers_ExploreTerm.get_type_info_from_type
              ret_ty in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range
                     "FStar.InteractiveHelpers.Effectful.fst"
                     (Prims.of_int (114)) (Prims.of_int (24))
                     (Prims.of_int (114)) (Prims.of_int (54)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range
                     "FStar.InteractiveHelpers.Effectful.fst"
                     (Prims.of_int (115)) (Prims.of_int (4))
                     (Prims.of_int (115)) (Prims.of_int (57)))))
            (Obj.magic uu___)
            (fun ret_type_info ->
               FStar_Tactics_Effect.lift_div_tac
                 (fun uu___1 ->
                    FStar_Pervasives_Native.Some
                      (mk_effect_info
                         FStar_InteractiveHelpers_ExploreTerm.E_Total
                         ret_type_info FStar_Pervasives_Native.None
                         FStar_Pervasives_Native.None)))
      | FStarC_Reflection_V1_Data.C_GTotal ret_ty ->
          let uu___ =
            FStar_InteractiveHelpers_ExploreTerm.get_type_info_from_type
              ret_ty in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range
                     "FStar.InteractiveHelpers.Effectful.fst"
                     (Prims.of_int (117)) (Prims.of_int (24))
                     (Prims.of_int (117)) (Prims.of_int (54)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range
                     "FStar.InteractiveHelpers.Effectful.fst"
                     (Prims.of_int (118)) (Prims.of_int (4))
                     (Prims.of_int (118)) (Prims.of_int (57)))))
            (Obj.magic uu___)
            (fun ret_type_info ->
               FStar_Tactics_Effect.lift_div_tac
                 (fun uu___1 ->
                    FStar_Pervasives_Native.Some
                      (mk_effect_info
                         FStar_InteractiveHelpers_ExploreTerm.E_Total
                         ret_type_info FStar_Pervasives_Native.None
                         FStar_Pervasives_Native.None)))
      | FStarC_Reflection_V1_Data.C_Lemma (pre, post, patterns) ->
          let uu___ = FStar_InteractiveHelpers_Base.prettify_term dbg pre in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range
                     "FStar.InteractiveHelpers.Effectful.fst"
                     (Prims.of_int (121)) (Prims.of_int (14))
                     (Prims.of_int (121)) (Prims.of_int (35)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range
                     "FStar.InteractiveHelpers.Effectful.fst"
                     (Prims.of_int (121)) (Prims.of_int (38))
                     (Prims.of_int (123)) (Prims.of_int (71)))))
            (Obj.magic uu___)
            (fun uu___1 ->
               (fun pre1 ->
                  let uu___1 =
                    FStar_InteractiveHelpers_Base.prettify_term dbg post in
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.InteractiveHelpers.Effectful.fst"
                                (Prims.of_int (122)) (Prims.of_int (15))
                                (Prims.of_int (122)) (Prims.of_int (37)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.InteractiveHelpers.Effectful.fst"
                                (Prims.of_int (123)) (Prims.of_int (4))
                                (Prims.of_int (123)) (Prims.of_int (71)))))
                       (Obj.magic uu___1)
                       (fun post1 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___2 ->
                               FStar_Pervasives_Native.Some
                                 (mk_effect_info
                                    FStar_InteractiveHelpers_ExploreTerm.E_Lemma
                                    FStar_InteractiveHelpers_ExploreTerm.unit_type_info
                                    (FStar_Pervasives_Native.Some pre1)
                                    (FStar_Pervasives_Native.Some post1))))))
                 uu___1)
      | FStarC_Reflection_V1_Data.C_Eff
          (univs, eff_name, ret_ty, eff_args, uu___) ->
          let uu___1 =
            FStar_InteractiveHelpers_Base.print_dbg dbg
              (Prims.strcat "comp_view_to_effect_info: C_Eff "
                 (FStar_Reflection_V1_Derived.flatten_name eff_name)) in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range
                     "FStar.InteractiveHelpers.Effectful.fst"
                     (Prims.of_int (125)) (Prims.of_int (4))
                     (Prims.of_int (125)) (Prims.of_int (78)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range
                     "FStar.InteractiveHelpers.Effectful.fst"
                     (Prims.of_int (125)) (Prims.of_int (79))
                     (Prims.of_int (142)) (Prims.of_int (7)))))
            (Obj.magic uu___1)
            (fun uu___2 ->
               (fun uu___2 ->
                  let uu___3 =
                    FStar_InteractiveHelpers_ExploreTerm.get_type_info_from_type
                      ret_ty in
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.InteractiveHelpers.Effectful.fst"
                                (Prims.of_int (126)) (Prims.of_int (24))
                                (Prims.of_int (126)) (Prims.of_int (54)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.InteractiveHelpers.Effectful.fst"
                                (Prims.of_int (126)) (Prims.of_int (57))
                                (Prims.of_int (142)) (Prims.of_int (7)))))
                       (Obj.magic uu___3)
                       (fun uu___4 ->
                          (fun ret_type_info ->
                             let uu___4 =
                               Obj.magic
                                 (FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___5 ->
                                       FStar_InteractiveHelpers_ExploreTerm.effect_name_to_type
                                         eff_name)) in
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "FStar.InteractiveHelpers.Effectful.fst"
                                           (Prims.of_int (127))
                                           (Prims.of_int (16))
                                           (Prims.of_int (127))
                                           (Prims.of_int (44)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "FStar.InteractiveHelpers.Effectful.fst"
                                           (Prims.of_int (127))
                                           (Prims.of_int (47))
                                           (Prims.of_int (142))
                                           (Prims.of_int (7)))))
                                  (Obj.magic uu___4)
                                  (fun uu___5 ->
                                     (fun etype ->
                                        let uu___5 =
                                          Obj.magic
                                            (FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___6 ->
                                                  mk_effect_info etype
                                                    ret_type_info)) in
                                        Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "FStar.InteractiveHelpers.Effectful.fst"
                                                      (Prims.of_int (128))
                                                      (Prims.of_int (17))
                                                      (Prims.of_int (128))
                                                      (Prims.of_int (51)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "FStar.InteractiveHelpers.Effectful.fst"
                                                      (Prims.of_int (128))
                                                      (Prims.of_int (54))
                                                      (Prims.of_int (142))
                                                      (Prims.of_int (7)))))
                                             (Obj.magic uu___5)
                                             (fun uu___6 ->
                                                (fun mk_res ->
                                                   let uu___6 =
                                                     FStar_Tactics_Util.map
                                                       (fun uu___7 ->
                                                          match uu___7 with
                                                          | (x, a) ->
                                                              let uu___8 =
                                                                FStar_InteractiveHelpers_Base.prettify_term
                                                                  dbg x in
                                                              FStar_Tactics_Effect.tac_bind
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (129))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (129))
                                                                    (Prims.of_int (57)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (129))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (129))
                                                                    (Prims.of_int (61)))))
                                                                (Obj.magic
                                                                   uu___8)
                                                                (fun uu___9
                                                                   ->
                                                                   FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (uu___9,
                                                                    a))))
                                                       eff_args in
                                                   Obj.magic
                                                     (FStar_Tactics_Effect.tac_bind
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "FStar.InteractiveHelpers.Effectful.fst"
                                                                 (Prims.of_int (129))
                                                                 (Prims.of_int (19))
                                                                 (Prims.of_int (129))
                                                                 (Prims.of_int (71)))))
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "FStar.InteractiveHelpers.Effectful.fst"
                                                                 (Prims.of_int (130))
                                                                 (Prims.of_int (10))
                                                                 (Prims.of_int (141))
                                                                 (Prims.of_int (15)))))
                                                        (Obj.magic uu___6)
                                                        (fun eff_args1 ->
                                                           FStar_Tactics_Effect.lift_div_tac
                                                             (fun uu___7 ->
                                                                match 
                                                                  (etype,
                                                                    eff_args1)
                                                                with
                                                                | (FStar_InteractiveHelpers_ExploreTerm.E_PURE,
                                                                   (pre,
                                                                    uu___8)::[])
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    (mk_res
                                                                    (FStar_Pervasives_Native.Some
                                                                    pre)
                                                                    FStar_Pervasives_Native.None)
                                                                | (FStar_InteractiveHelpers_ExploreTerm.E_Pure,
                                                                   (pre,
                                                                    uu___8)::
                                                                   (post,
                                                                    uu___9)::[])
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    (mk_res
                                                                    (FStar_Pervasives_Native.Some
                                                                    pre)
                                                                    (FStar_Pervasives_Native.Some
                                                                    post))
                                                                | (FStar_InteractiveHelpers_ExploreTerm.E_Stack,
                                                                   (pre,
                                                                    uu___8)::
                                                                   (post,
                                                                    uu___9)::[])
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    (mk_res
                                                                    (FStar_Pervasives_Native.Some
                                                                    pre)
                                                                    (FStar_Pervasives_Native.Some
                                                                    post))
                                                                | (FStar_InteractiveHelpers_ExploreTerm.E_ST,
                                                                   (pre,
                                                                    uu___8)::
                                                                   (post,
                                                                    uu___9)::[])
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    (mk_res
                                                                    (FStar_Pervasives_Native.Some
                                                                    pre)
                                                                    (FStar_Pervasives_Native.Some
                                                                    post))
                                                                | (FStar_InteractiveHelpers_ExploreTerm.E_Unknown,
                                                                   []) ->
                                                                    FStar_Pervasives_Native.Some
                                                                    (mk_res
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Pervasives_Native.None)
                                                                | (FStar_InteractiveHelpers_ExploreTerm.E_Unknown,
                                                                   (pre,
                                                                    uu___8)::[])
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    (mk_res
                                                                    (FStar_Pervasives_Native.Some
                                                                    pre)
                                                                    FStar_Pervasives_Native.None)
                                                                | (FStar_InteractiveHelpers_ExploreTerm.E_Unknown,
                                                                   (pre,
                                                                    uu___8)::
                                                                   (post,
                                                                    uu___9)::[])
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    (mk_res
                                                                    (FStar_Pervasives_Native.Some
                                                                    pre)
                                                                    (FStar_Pervasives_Native.Some
                                                                    post))
                                                                | uu___8 ->
                                                                    FStar_Pervasives_Native.None))))
                                                  uu___6))) uu___5))) uu___4)))
                 uu___2)
let (comp_to_effect_info :
  Prims.bool ->
    FStarC_Reflection_Types.comp ->
      (effect_info FStar_Pervasives_Native.option, unit)
        FStar_Tactics_Effect.tac_repr)
  =
  fun dbg ->
    fun c ->
      let uu___ =
        Obj.magic
          (FStar_Tactics_Effect.lift_div_tac
             (fun uu___1 -> FStarC_Reflection_V1_Builtins.inspect_comp c)) in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.InteractiveHelpers.Effectful.fst"
                 (Prims.of_int (147)) (Prims.of_int (23))
                 (Prims.of_int (147)) (Prims.of_int (37)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.InteractiveHelpers.Effectful.fst"
                 (Prims.of_int (148)) (Prims.of_int (2)) (Prims.of_int (148))
                 (Prims.of_int (33))))) (Obj.magic uu___)
        (fun uu___1 ->
           (fun cv -> Obj.magic (comp_view_to_effect_info dbg cv)) uu___1)
let (compute_effect_info :
  Prims.bool ->
    FStarC_Reflection_Types.env ->
      FStarC_Reflection_Types.term ->
        (effect_info FStar_Pervasives_Native.option, unit)
          FStar_Tactics_Effect.tac_repr)
  =
  fun dbg ->
    fun e ->
      fun tm ->
        let uu___ = FStar_InteractiveHelpers_ExploreTerm.safe_tcc e tm in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range
                   "FStar.InteractiveHelpers.Effectful.fst"
                   (Prims.of_int (153)) (Prims.of_int (8))
                   (Prims.of_int (153)) (Prims.of_int (21)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range
                   "FStar.InteractiveHelpers.Effectful.fst"
                   (Prims.of_int (153)) (Prims.of_int (2))
                   (Prims.of_int (155)) (Prims.of_int (16)))))
          (Obj.magic uu___)
          (fun uu___1 ->
             (fun uu___1 ->
                match uu___1 with
                | FStar_Pervasives_Native.Some c ->
                    Obj.magic (Obj.repr (comp_to_effect_info dbg c))
                | FStar_Pervasives_Native.None ->
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___2 -> FStar_Pervasives_Native.None))))
               uu___1)
let (typ_or_comp_to_effect_info :
  Prims.bool ->
    FStar_InteractiveHelpers_Base.genv ->
      FStar_InteractiveHelpers_ExploreTerm.typ_or_comp ->
        (effect_info, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun dbg ->
    fun ge ->
      fun c ->
        let uu___ =
          FStar_InteractiveHelpers_ExploreTerm.flush_typ_or_comp dbg
            ge.FStar_InteractiveHelpers_Base.env c in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range
                   "FStar.InteractiveHelpers.Effectful.fst"
                   (Prims.of_int (170)) (Prims.of_int (10))
                   (Prims.of_int (170)) (Prims.of_int (40)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range
                   "FStar.InteractiveHelpers.Effectful.fst"
                   (Prims.of_int (171)) (Prims.of_int (2))
                   (Prims.of_int (179)) (Prims.of_int (25)))))
          (Obj.magic uu___)
          (fun uu___1 ->
             (fun c1 ->
                match c1 with
                | FStar_InteractiveHelpers_ExploreTerm.TC_Typ
                    (ty, uu___1, uu___2) ->
                    let uu___3 =
                      FStar_InteractiveHelpers_ExploreTerm.get_type_info_from_type
                        ty in
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.InteractiveHelpers.Effectful.fst"
                                  (Prims.of_int (173)) (Prims.of_int (16))
                                  (Prims.of_int (173)) (Prims.of_int (42)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.InteractiveHelpers.Effectful.fst"
                                  (Prims.of_int (174)) (Prims.of_int (4))
                                  (Prims.of_int (174)) (Prims.of_int (42)))))
                         (Obj.magic uu___3)
                         (fun tinfo ->
                            FStar_Tactics_Effect.lift_div_tac
                              (fun uu___4 ->
                                 mk_effect_info
                                   FStar_InteractiveHelpers_ExploreTerm.E_Total
                                   tinfo FStar_Pervasives_Native.None
                                   FStar_Pervasives_Native.None)))
                | FStar_InteractiveHelpers_ExploreTerm.TC_Comp
                    (cv, uu___1, uu___2) ->
                    let uu___3 = comp_to_effect_info dbg cv in
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.InteractiveHelpers.Effectful.fst"
                                  (Prims.of_int (176)) (Prims.of_int (20))
                                  (Prims.of_int (176)) (Prims.of_int (46)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.InteractiveHelpers.Effectful.fst"
                                  (Prims.of_int (177)) (Prims.of_int (4))
                                  (Prims.of_int (179)) (Prims.of_int (25)))))
                         (Obj.magic uu___3)
                         (fun uu___4 ->
                            (fun opt_einfo ->
                               match opt_einfo with
                               | FStar_Pervasives_Native.None ->
                                   Obj.magic
                                     (Obj.repr
                                        (let uu___4 =
                                           let uu___5 =
                                             FStar_InteractiveHelpers_Base.acomp_to_string
                                               cv in
                                           FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "FStar.InteractiveHelpers.Effectful.fst"
                                                      (Prims.of_int (178))
                                                      (Prims.of_int (64))
                                                      (Prims.of_int (178))
                                                      (Prims.of_int (82)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Prims.fst"
                                                      (Prims.of_int (611))
                                                      (Prims.of_int (19))
                                                      (Prims.of_int (611))
                                                      (Prims.of_int (31)))))
                                             (Obj.magic uu___5)
                                             (fun uu___6 ->
                                                FStar_Tactics_Effect.lift_div_tac
                                                  (fun uu___7 ->
                                                     Prims.strcat
                                                       "typ_or_comp_to_effect_info failed on: "
                                                       uu___6)) in
                                         FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                    (Prims.of_int (178))
                                                    (Prims.of_int (20))
                                                    (Prims.of_int (178))
                                                    (Prims.of_int (83)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                    (Prims.of_int (178))
                                                    (Prims.of_int (14))
                                                    (Prims.of_int (178))
                                                    (Prims.of_int (83)))))
                                           (Obj.magic uu___4)
                                           (fun uu___5 ->
                                              (fun uu___5 ->
                                                 Obj.magic
                                                   (FStar_InteractiveHelpers_Base.mfail
                                                      uu___5)) uu___5)))
                               | FStar_Pervasives_Native.Some einfo ->
                                   Obj.magic
                                     (Obj.repr
                                        (FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___4 -> einfo)))) uu___4)))
               uu___1)
let (tcc_no_lift :
  FStarC_Reflection_Types.env ->
    FStarC_Reflection_Types.term ->
      (FStarC_Reflection_Types.comp, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun e ->
    fun t ->
      let uu___ = FStarC_Tactics_V1_Builtins.inspect t in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.InteractiveHelpers.Effectful.fst"
                 (Prims.of_int (192)) (Prims.of_int (8)) (Prims.of_int (192))
                 (Prims.of_int (17)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.InteractiveHelpers.Effectful.fst"
                 (Prims.of_int (192)) (Prims.of_int (2)) (Prims.of_int (199))
                 (Prims.of_int (11))))) (Obj.magic uu___)
        (fun uu___1 ->
           (fun uu___1 ->
              match uu___1 with
              | FStarC_Reflection_V1_Data.Tv_App (uu___2, uu___3) ->
                  let uu___4 = FStar_Tactics_V1_SyntaxHelpers.collect_app t in
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.InteractiveHelpers.Effectful.fst"
                                (Prims.of_int (194)) (Prims.of_int (19))
                                (Prims.of_int (194)) (Prims.of_int (32)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.InteractiveHelpers.Effectful.fst"
                                (Prims.of_int (193)) (Prims.of_int (17))
                                (Prims.of_int (196)) (Prims.of_int (41)))))
                       (Obj.magic uu___4)
                       (fun uu___5 ->
                          (fun uu___5 ->
                             match uu___5 with
                             | (hd, args) ->
                                 let uu___6 =
                                   FStarC_Tactics_V1_Builtins.tcc e hd in
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "FStar.InteractiveHelpers.Effectful.fst"
                                               (Prims.of_int (195))
                                               (Prims.of_int (12))
                                               (Prims.of_int (195))
                                               (Prims.of_int (20)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "FStar.InteractiveHelpers.Effectful.fst"
                                               (Prims.of_int (196))
                                               (Prims.of_int (4))
                                               (Prims.of_int (196))
                                               (Prims.of_int (41)))))
                                      (Obj.magic uu___6)
                                      (fun uu___7 ->
                                         (fun c ->
                                            Obj.magic
                                              (FStar_InteractiveHelpers_ExploreTerm.inst_comp
                                                 e c
                                                 (FStar_List_Tot_Base.map
                                                    FStar_Pervasives_Native.fst
                                                    args))) uu___7))) uu___5))
              | uu___2 -> Obj.magic (FStarC_Tactics_V1_Builtins.tcc e t))
             uu___1)
let (compute_eterm_info :
  Prims.bool ->
    FStarC_Reflection_Types.env ->
      FStarC_Reflection_Types.term ->
        (eterm_info, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun dbg ->
    fun e ->
      fun t ->
        let uu___ = decompose_application e t in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range
                   "FStar.InteractiveHelpers.Effectful.fst"
                   (Prims.of_int (207)) (Prims.of_int (23))
                   (Prims.of_int (207)) (Prims.of_int (48)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range
                   "FStar.InteractiveHelpers.Effectful.fst"
                   (Prims.of_int (205)) (Prims.of_int (58))
                   (Prims.of_int (220)) (Prims.of_int (16)))))
          (Obj.magic uu___)
          (fun uu___1 ->
             (fun uu___1 ->
                match uu___1 with
                | (hd, parameters) ->
                    Obj.magic
                      (FStar_Tactics_V1_Derived.try_with
                         (fun uu___2 ->
                            match () with
                            | () ->
                                let uu___3 = tcc_no_lift e t in
                                FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "FStar.InteractiveHelpers.Effectful.fst"
                                           (Prims.of_int (210))
                                           (Prims.of_int (19))
                                           (Prims.of_int (210))
                                           (Prims.of_int (34)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "FStar.InteractiveHelpers.Effectful.fst"
                                           (Prims.of_int (210))
                                           (Prims.of_int (37))
                                           (Prims.of_int (215))
                                           (Prims.of_int (39)))))
                                  (Obj.magic uu___3)
                                  (fun uu___4 ->
                                     (fun c ->
                                        let uu___4 =
                                          comp_to_effect_info dbg c in
                                        Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "FStar.InteractiveHelpers.Effectful.fst"
                                                      (Prims.of_int (211))
                                                      (Prims.of_int (20))
                                                      (Prims.of_int (211))
                                                      (Prims.of_int (45)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "FStar.InteractiveHelpers.Effectful.fst"
                                                      (Prims.of_int (212))
                                                      (Prims.of_int (4))
                                                      (Prims.of_int (215))
                                                      (Prims.of_int (39)))))
                                             (Obj.magic uu___4)
                                             (fun uu___5 ->
                                                (fun opt_einfo ->
                                                   match opt_einfo with
                                                   | FStar_Pervasives_Native.None
                                                       ->
                                                       Obj.magic
                                                         (Obj.repr
                                                            (let uu___5 =
                                                               let uu___6 =
                                                                 FStarC_Tactics_V1_Builtins.term_to_string
                                                                   t in
                                                               FStar_Tactics_Effect.tac_bind
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (213))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (213))
                                                                    (Prims.of_int (73)))))
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                 (Obj.magic
                                                                    uu___6)
                                                                 (fun uu___7
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    Prims.strcat
                                                                    "compute_eterm_info: failed on: "
                                                                    uu___7)) in
                                                             FStar_Tactics_Effect.tac_bind
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (213))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (213))
                                                                    (Prims.of_int (74)))))
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (213))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (213))
                                                                    (Prims.of_int (74)))))
                                                               (Obj.magic
                                                                  uu___5)
                                                               (fun uu___6 ->
                                                                  (fun uu___6
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.mfail
                                                                    uu___6))
                                                                    uu___6)))
                                                   | FStar_Pervasives_Native.Some
                                                       einfo ->
                                                       Obj.magic
                                                         (Obj.repr
                                                            (FStar_Tactics_Effect.lift_div_tac
                                                               (fun uu___5 ->
                                                                  mk_eterm_info
                                                                    einfo hd
                                                                    parameters))))
                                                  uu___5))) uu___4))
                         (fun uu___2 ->
                            (fun uu___2 ->
                               match uu___2 with
                               | FStarC_Tactics_Common.TacticFailure
                                   (msg, uu___3) ->
                                   Obj.magic
                                     (Obj.repr
                                        (FStar_InteractiveHelpers_Base.mfail_doc
                                           (FStar_List_Tot_Base.op_At
                                              [FStarC_Pprint.arbitrary_string
                                                 "compute_eterm_info: failure"]
                                              msg)))
                               | e1 ->
                                   Obj.magic
                                     (Obj.repr
                                        (FStar_Tactics_Effect.raise e1)))
                              uu___2))) uu___1)
let (has_refinement :
  FStar_InteractiveHelpers_ExploreTerm.type_info -> Prims.bool) =
  fun ty ->
    FStar_Pervasives_Native.uu___is_Some
      ty.FStar_InteractiveHelpers_ExploreTerm.refin
let (get_refinement :
  FStar_InteractiveHelpers_ExploreTerm.type_info ->
    FStarC_Reflection_Types.term)
  =
  fun ty ->
    FStar_Pervasives_Native.__proj__Some__item__v
      ty.FStar_InteractiveHelpers_ExploreTerm.refin
let (get_opt_refinment :
  FStar_InteractiveHelpers_ExploreTerm.type_info ->
    FStarC_Reflection_Types.term FStar_Pervasives_Native.option)
  = fun ty -> ty.FStar_InteractiveHelpers_ExploreTerm.refin
let (get_rawest_type :
  FStar_InteractiveHelpers_ExploreTerm.type_info ->
    FStarC_Reflection_Types.typ)
  = fun ty -> ty.FStar_InteractiveHelpers_ExploreTerm.ty
type type_comparison =
  | Refines 
  | Same_raw_type 
  | Unknown 
let (uu___is_Refines : type_comparison -> Prims.bool) =
  fun projectee -> match projectee with | Refines -> true | uu___ -> false
let (uu___is_Same_raw_type : type_comparison -> Prims.bool) =
  fun projectee ->
    match projectee with | Same_raw_type -> true | uu___ -> false
let (uu___is_Unknown : type_comparison -> Prims.bool) =
  fun projectee -> match projectee with | Unknown -> true | uu___ -> false
let (type_comparison_to_string : type_comparison -> Prims.string) =
  fun c ->
    match c with
    | Refines -> "Refines"
    | Same_raw_type -> "Same_raw_type"
    | Unknown -> "Unknown"
let (compare_types :
  Prims.bool ->
    FStar_InteractiveHelpers_ExploreTerm.type_info ->
      FStar_InteractiveHelpers_ExploreTerm.type_info ->
        (type_comparison, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun dbg ->
    fun info1 ->
      fun info2 ->
        let uu___ =
          FStar_InteractiveHelpers_Base.print_dbg dbg "[> compare_types" in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range
                   "FStar.InteractiveHelpers.Effectful.fst"
                   (Prims.of_int (252)) (Prims.of_int (2))
                   (Prims.of_int (252)) (Prims.of_int (34)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range
                   "FStar.InteractiveHelpers.Effectful.fst"
                   (Prims.of_int (253)) (Prims.of_int (2))
                   (Prims.of_int (276)) (Prims.of_int (13)))))
          (Obj.magic uu___)
          (fun uu___1 ->
             (fun uu___1 ->
                if
                  term_eq info1.FStar_InteractiveHelpers_ExploreTerm.ty
                    info2.FStar_InteractiveHelpers_ExploreTerm.ty
                then
                  let uu___2 =
                    FStar_InteractiveHelpers_Base.print_dbg dbg
                      "-> types are equal" in
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.InteractiveHelpers.Effectful.fst"
                                (Prims.of_int (254)) (Prims.of_int (14))
                                (Prims.of_int (254)) (Prims.of_int (48)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.InteractiveHelpers.Effectful.fst"
                                (Prims.of_int (255)) (Prims.of_int (6))
                                (Prims.of_int (273)) (Prims.of_int (15)))))
                       (Obj.magic uu___2)
                       (fun uu___3 ->
                          (fun uu___3 ->
                             if has_refinement info2
                             then
                               let uu___4 =
                                 FStar_InteractiveHelpers_Base.print_dbg dbg
                                   "-> 2nd type has refinement" in
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.InteractiveHelpers.Effectful.fst"
                                             (Prims.of_int (256))
                                             (Prims.of_int (16))
                                             (Prims.of_int (256))
                                             (Prims.of_int (58)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.InteractiveHelpers.Effectful.fst"
                                             (Prims.of_int (259))
                                             (Prims.of_int (8))
                                             (Prims.of_int (270))
                                             (Prims.of_int (23)))))
                                    (Obj.magic uu___4)
                                    (fun uu___5 ->
                                       (fun uu___5 ->
                                          if has_refinement info1
                                          then
                                            let uu___6 =
                                              FStar_InteractiveHelpers_Base.print_dbg
                                                dbg
                                                "-> 1st type has refinement" in
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "FStar.InteractiveHelpers.Effectful.fst"
                                                          (Prims.of_int (260))
                                                          (Prims.of_int (18))
                                                          (Prims.of_int (260))
                                                          (Prims.of_int (60)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "FStar.InteractiveHelpers.Effectful.fst"
                                                          (Prims.of_int (261))
                                                          (Prims.of_int (10))
                                                          (Prims.of_int (266))
                                                          (Prims.of_int (23)))))
                                                 (Obj.magic uu___6)
                                                 (fun uu___7 ->
                                                    (fun uu___7 ->
                                                       if
                                                         term_eq
                                                           (get_refinement
                                                              info1)
                                                           (get_refinement
                                                              info2)
                                                       then
                                                         let uu___8 =
                                                           FStar_InteractiveHelpers_Base.print_dbg
                                                             dbg "-> Refines" in
                                                         Obj.magic
                                                           (FStar_Tactics_Effect.tac_bind
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (262))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (262))
                                                                    (Prims.of_int (46)))))
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (263))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (263))
                                                                    (Prims.of_int (19)))))
                                                              (Obj.magic
                                                                 uu___8)
                                                              (fun uu___9 ->
                                                                 FStar_Tactics_Effect.lift_div_tac
                                                                   (fun
                                                                    uu___10
                                                                    ->
                                                                    Refines)))
                                                       else
                                                         (let uu___9 =
                                                            FStar_InteractiveHelpers_Base.print_dbg
                                                              dbg
                                                              "-> Same_raw_type" in
                                                          Obj.magic
                                                            (FStar_Tactics_Effect.tac_bind
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (265))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (265))
                                                                    (Prims.of_int (50)))))
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (266))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (266))
                                                                    (Prims.of_int (23)))))
                                                               (Obj.magic
                                                                  uu___9)
                                                               (fun uu___10
                                                                  ->
                                                                  FStar_Tactics_Effect.lift_div_tac
                                                                    (
                                                                    fun
                                                                    uu___11
                                                                    ->
                                                                    Same_raw_type)))))
                                                      uu___7))
                                          else
                                            (let uu___7 =
                                               FStar_InteractiveHelpers_Base.print_dbg
                                                 dbg
                                                 "-> 1st type has no refinement" in
                                             Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.InteractiveHelpers.Effectful.fst"
                                                           (Prims.of_int (268))
                                                           (Prims.of_int (18))
                                                           (Prims.of_int (268))
                                                           (Prims.of_int (63)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.InteractiveHelpers.Effectful.fst"
                                                           (Prims.of_int (268))
                                                           (Prims.of_int (66))
                                                           (Prims.of_int (270))
                                                           (Prims.of_int (23)))))
                                                  (Obj.magic uu___7)
                                                  (fun uu___8 ->
                                                     (fun uu___8 ->
                                                        let uu___9 =
                                                          FStar_InteractiveHelpers_Base.print_dbg
                                                            dbg
                                                            "-> Same_raw_type" in
                                                        Obj.magic
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (269))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (269))
                                                                    (Prims.of_int (50)))))
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (270))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (270))
                                                                    (Prims.of_int (23)))))
                                                             (Obj.magic
                                                                uu___9)
                                                             (fun uu___10 ->
                                                                FStar_Tactics_Effect.lift_div_tac
                                                                  (fun
                                                                    uu___11
                                                                    ->
                                                                    Same_raw_type))))
                                                       uu___8)))) uu___5))
                             else
                               (let uu___5 =
                                  FStar_InteractiveHelpers_Base.print_dbg dbg
                                    "-> 2nd type has no refinement: Refines" in
                                Obj.magic
                                  (FStar_Tactics_Effect.tac_bind
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "FStar.InteractiveHelpers.Effectful.fst"
                                              (Prims.of_int (272))
                                              (Prims.of_int (16))
                                              (Prims.of_int (272))
                                              (Prims.of_int (70)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "FStar.InteractiveHelpers.Effectful.fst"
                                              (Prims.of_int (273))
                                              (Prims.of_int (8))
                                              (Prims.of_int (273))
                                              (Prims.of_int (15)))))
                                     (Obj.magic uu___5)
                                     (fun uu___6 ->
                                        FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___7 -> Refines))))) uu___3))
                else
                  (let uu___3 =
                     FStar_InteractiveHelpers_Base.print_dbg dbg
                       "types are not equal" in
                   Obj.magic
                     (FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.InteractiveHelpers.Effectful.fst"
                                 (Prims.of_int (275)) (Prims.of_int (14))
                                 (Prims.of_int (275)) (Prims.of_int (49)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.InteractiveHelpers.Effectful.fst"
                                 (Prims.of_int (276)) (Prims.of_int (6))
                                 (Prims.of_int (276)) (Prims.of_int (13)))))
                        (Obj.magic uu___3)
                        (fun uu___4 ->
                           FStar_Tactics_Effect.lift_div_tac
                             (fun uu___5 -> Unknown))))) uu___1)
let (compare_cast_types :
  Prims.bool ->
    cast_info -> (type_comparison, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun dbg ->
    fun p ->
      let uu___ =
        FStar_InteractiveHelpers_Base.print_dbg dbg "[> compare_cast_types" in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.InteractiveHelpers.Effectful.fst"
                 (Prims.of_int (282)) (Prims.of_int (2)) (Prims.of_int (282))
                 (Prims.of_int (39)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.InteractiveHelpers.Effectful.fst"
                 (Prims.of_int (283)) (Prims.of_int (2)) (Prims.of_int (286))
                 (Prims.of_int (16))))) (Obj.magic uu___)
        (fun uu___1 ->
           (fun uu___1 ->
              match ((p.p_ty), (p.exp_ty)) with
              | (FStar_Pervasives_Native.Some info1,
                 FStar_Pervasives_Native.Some info2) ->
                  Obj.magic (Obj.repr (compare_types dbg info1 info2))
              | uu___2 ->
                  Obj.magic
                    (Obj.repr
                       (FStar_Tactics_Effect.lift_div_tac
                          (fun uu___3 -> Unknown)))) uu___1)
let (mk_has_type :
  FStarC_Reflection_Types.term ->
    FStarC_Reflection_Types.typ ->
      (FStarC_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun t ->
         fun ty ->
           Obj.magic
             (FStar_Tactics_Effect.lift_div_tac
                (fun uu___ ->
                   FStar_Reflection_V1_Derived.mk_app
                     (FStarC_Reflection_V2_Builtins.pack_ln
                        (FStarC_Reflection_V2_Data.Tv_FVar
                           (FStarC_Reflection_V2_Builtins.pack_fv
                              ["Prims"; "has_type"])))
                     [(ty, FStarC_Reflection_V1_Data.Q_Implicit);
                     (t, FStarC_Reflection_V1_Data.Q_Explicit);
                     (ty, FStarC_Reflection_V1_Data.Q_Explicit)]))) uu___1
        uu___
let (cast_info_to_propositions :
  Prims.bool ->
    FStar_InteractiveHelpers_Base.genv ->
      cast_info ->
        (FStar_InteractiveHelpers_Propositions.proposition Prims.list, 
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun dbg ->
    fun ge ->
      fun ci ->
        let uu___ =
          let uu___1 =
            let uu___2 = cast_info_to_string ci in
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range
                       "FStar.InteractiveHelpers.Effectful.fst"
                       (Prims.of_int (313)) (Prims.of_int (53))
                       (Prims.of_int (313)) (Prims.of_int (75)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Prims.fst" (Prims.of_int (611))
                       (Prims.of_int (19)) (Prims.of_int (611))
                       (Prims.of_int (31))))) (Obj.magic uu___2)
              (fun uu___3 ->
                 FStar_Tactics_Effect.lift_div_tac
                   (fun uu___4 ->
                      Prims.strcat "[> cast_info_to_propositions:\n" uu___3)) in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range
                     "FStar.InteractiveHelpers.Effectful.fst"
                     (Prims.of_int (313)) (Prims.of_int (16))
                     (Prims.of_int (313)) (Prims.of_int (76)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range
                     "FStar.InteractiveHelpers.Effectful.fst"
                     (Prims.of_int (313)) (Prims.of_int (2))
                     (Prims.of_int (313)) (Prims.of_int (76)))))
            (Obj.magic uu___1)
            (fun uu___2 ->
               (fun uu___2 ->
                  Obj.magic
                    (FStar_InteractiveHelpers_Base.print_dbg dbg uu___2))
                 uu___2) in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range
                   "FStar.InteractiveHelpers.Effectful.fst"
                   (Prims.of_int (313)) (Prims.of_int (2))
                   (Prims.of_int (313)) (Prims.of_int (76)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range
                   "FStar.InteractiveHelpers.Effectful.fst"
                   (Prims.of_int (314)) (Prims.of_int (2))
                   (Prims.of_int (341)) (Prims.of_int (13)))))
          (Obj.magic uu___)
          (fun uu___1 ->
             (fun uu___1 ->
                let uu___2 = compare_cast_types dbg ci in
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.InteractiveHelpers.Effectful.fst"
                              (Prims.of_int (314)) (Prims.of_int (8))
                              (Prims.of_int (314)) (Prims.of_int (33)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.InteractiveHelpers.Effectful.fst"
                              (Prims.of_int (314)) (Prims.of_int (2))
                              (Prims.of_int (341)) (Prims.of_int (13)))))
                     (Obj.magic uu___2)
                     (fun uu___3 ->
                        (fun uu___3 ->
                           match uu___3 with
                           | Refines ->
                               let uu___4 =
                                 FStar_InteractiveHelpers_Base.print_dbg dbg
                                   "-> Comparison result: Refines" in
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.InteractiveHelpers.Effectful.fst"
                                             (Prims.of_int (316))
                                             (Prims.of_int (4))
                                             (Prims.of_int (316))
                                             (Prims.of_int (51)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.InteractiveHelpers.Effectful.fst"
                                             (Prims.of_int (317))
                                             (Prims.of_int (4))
                                             (Prims.of_int (317))
                                             (Prims.of_int (6)))))
                                    (Obj.magic uu___4)
                                    (fun uu___5 ->
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___6 -> [])))
                           | Same_raw_type ->
                               let uu___4 =
                                 FStar_InteractiveHelpers_Base.print_dbg dbg
                                   "-> Comparison result: Same_raw_type" in
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.InteractiveHelpers.Effectful.fst"
                                             (Prims.of_int (319))
                                             (Prims.of_int (4))
                                             (Prims.of_int (319))
                                             (Prims.of_int (57)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.InteractiveHelpers.Effectful.fst"
                                             (Prims.of_int (319))
                                             (Prims.of_int (58))
                                             (Prims.of_int (322))
                                             (Prims.of_int (16)))))
                                    (Obj.magic uu___4)
                                    (fun uu___5 ->
                                       (fun uu___5 ->
                                          let uu___6 =
                                            Obj.magic
                                              (FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___7 ->
                                                    get_refinement
                                                      (FStar_Pervasives_Native.__proj__Some__item__v
                                                         ci.exp_ty))) in
                                          Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "FStar.InteractiveHelpers.Effectful.fst"
                                                        (Prims.of_int (320))
                                                        (Prims.of_int (16))
                                                        (Prims.of_int (320))
                                                        (Prims.of_int (50)))))
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "FStar.InteractiveHelpers.Effectful.fst"
                                                        (Prims.of_int (320))
                                                        (Prims.of_int (53))
                                                        (Prims.of_int (322))
                                                        (Prims.of_int (16)))))
                                               (Obj.magic uu___6)
                                               (fun uu___7 ->
                                                  (fun refin ->
                                                     let uu___7 =
                                                       FStar_InteractiveHelpers_Base.mk_app_norm
                                                         ge.FStar_InteractiveHelpers_Base.env
                                                         refin [ci.term] in
                                                     Obj.magic
                                                       (FStar_Tactics_Effect.tac_bind
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "FStar.InteractiveHelpers.Effectful.fst"
                                                                   (Prims.of_int (321))
                                                                   (Prims.of_int (21))
                                                                   (Prims.of_int (321))
                                                                   (Prims.of_int (55)))))
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "FStar.InteractiveHelpers.Effectful.fst"
                                                                   (Prims.of_int (322))
                                                                   (Prims.of_int (4))
                                                                   (Prims.of_int (322))
                                                                   (Prims.of_int (16)))))
                                                          (Obj.magic uu___7)
                                                          (fun inst_refin ->
                                                             FStar_Tactics_Effect.lift_div_tac
                                                               (fun uu___8 ->
                                                                  [inst_refin]))))
                                                    uu___7))) uu___5))
                           | Unknown ->
                               let uu___4 =
                                 FStar_InteractiveHelpers_Base.print_dbg dbg
                                   "-> Comparison result: Unknown" in
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.InteractiveHelpers.Effectful.fst"
                                             (Prims.of_int (324))
                                             (Prims.of_int (4))
                                             (Prims.of_int (324))
                                             (Prims.of_int (51)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.InteractiveHelpers.Effectful.fst"
                                             (Prims.of_int (325))
                                             (Prims.of_int (4))
                                             (Prims.of_int (341))
                                             (Prims.of_int (13)))))
                                    (Obj.magic uu___4)
                                    (fun uu___5 ->
                                       (fun uu___5 ->
                                          match ((ci.p_ty), (ci.exp_ty)) with
                                          | (FStar_Pervasives_Native.Some
                                             p_ty,
                                             FStar_Pervasives_Native.Some
                                             e_ty) ->
                                              Obj.magic
                                                (Obj.repr
                                                   (let uu___6 =
                                                      Obj.magic
                                                        (FStar_Tactics_Effect.lift_div_tac
                                                           (fun uu___7 ->
                                                              get_rawest_type
                                                                p_ty)) in
                                                    FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "FStar.InteractiveHelpers.Effectful.fst"
                                                               (Prims.of_int (327))
                                                               (Prims.of_int (18))
                                                               (Prims.of_int (327))
                                                               (Prims.of_int (38)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "FStar.InteractiveHelpers.Effectful.fst"
                                                               (Prims.of_int (327))
                                                               (Prims.of_int (41))
                                                               (Prims.of_int (340))
                                                               (Prims.of_int (41)))))
                                                      (Obj.magic uu___6)
                                                      (fun uu___7 ->
                                                         (fun p_rty ->
                                                            let uu___7 =
                                                              Obj.magic
                                                                (FStar_Tactics_Effect.lift_div_tac
                                                                   (fun
                                                                    uu___8 ->
                                                                    get_rawest_type
                                                                    e_ty)) in
                                                            Obj.magic
                                                              (FStar_Tactics_Effect.tac_bind
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (328))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (328))
                                                                    (Prims.of_int (38)))))
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (328))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (340))
                                                                    (Prims.of_int (41)))))
                                                                 (Obj.magic
                                                                    uu___7)
                                                                 (fun uu___8
                                                                    ->
                                                                    (fun
                                                                    e_rty ->
                                                                    let uu___8
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.pack
                                                                    (FStarC_Reflection_V1_Data.Tv_AscribedT
                                                                    ((ci.term),
                                                                    p_rty,
                                                                    FStar_Pervasives_Native.None,
                                                                    false)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (335))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (335))
                                                                    (Prims.of_int (66)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (335))
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (340))
                                                                    (Prims.of_int (41)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    ascr_term
                                                                    ->
                                                                    let uu___9
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    [
                                                                    (p_rty,
                                                                    FStarC_Reflection_V1_Data.Q_Implicit);
                                                                    (ascr_term,
                                                                    FStarC_Reflection_V1_Data.Q_Explicit);
                                                                    (e_rty,
                                                                    FStarC_Reflection_V1_Data.Q_Explicit)])) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (336))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (336))
                                                                    (Prims.of_int (95)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (336))
                                                                    (Prims.of_int (98))
                                                                    (Prims.of_int (340))
                                                                    (Prims.of_int (41)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    has_type_params
                                                                    ->
                                                                    let uu___10
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Reflection_V1_Derived.mk_app
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["Prims";
                                                                    "has_type"])))
                                                                    has_type_params)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (337))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (337))
                                                                    (Prims.of_int (56)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (337))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (340))
                                                                    (Prims.of_int (41)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    type_cast
                                                                    ->
                                                                    let uu___11
                                                                    =
                                                                    FStar_InteractiveHelpers_Base.opt_mk_app_norm
                                                                    ge.FStar_InteractiveHelpers_Base.env
                                                                    e_ty.FStar_InteractiveHelpers_ExploreTerm.refin
                                                                    [ci.term] in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (339))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (339))
                                                                    (Prims.of_int (70)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (340))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (340))
                                                                    (Prims.of_int (41)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    inst_opt_refin
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_InteractiveHelpers_Base.opt_cons
                                                                    inst_opt_refin
                                                                    [type_cast]))))
                                                                    uu___11)))
                                                                    uu___10)))
                                                                    uu___9)))
                                                                    uu___8)))
                                                           uu___7)))
                                          | uu___6 ->
                                              Obj.magic
                                                (Obj.repr
                                                   (FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___7 -> []))))
                                         uu___5))) uu___3))) uu___1)
let (cast_info_list_to_propositions :
  Prims.bool ->
    FStar_InteractiveHelpers_Base.genv ->
      cast_info Prims.list ->
        (FStar_InteractiveHelpers_Propositions.proposition Prims.list, 
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun dbg ->
    fun ge ->
      fun ls ->
        let uu___ =
          FStar_Tactics_Util.map (cast_info_to_propositions dbg ge) ls in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range
                   "FStar.InteractiveHelpers.Effectful.fst"
                   (Prims.of_int (348)) (Prims.of_int (12))
                   (Prims.of_int (348)) (Prims.of_int (53)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range
                   "FStar.InteractiveHelpers.Effectful.fst"
                   (Prims.of_int (349)) (Prims.of_int (2))
                   (Prims.of_int (349)) (Prims.of_int (13)))))
          (Obj.magic uu___)
          (fun lsl1 ->
             FStar_Tactics_Effect.lift_div_tac
               (fun uu___1 -> FStar_List_Tot_Base.flatten lsl1))
type pre_post_type =
  | PP_Unknown 
  | PP_Pure 
  | PP_State of FStarC_Reflection_Types.term 
let (uu___is_PP_Unknown : pre_post_type -> Prims.bool) =
  fun projectee -> match projectee with | PP_Unknown -> true | uu___ -> false
let (uu___is_PP_Pure : pre_post_type -> Prims.bool) =
  fun projectee -> match projectee with | PP_Pure -> true | uu___ -> false
let (uu___is_PP_State : pre_post_type -> Prims.bool) =
  fun projectee ->
    match projectee with | PP_State state_type -> true | uu___ -> false
let (__proj__PP_State__item__state_type :
  pre_post_type -> FStarC_Reflection_Types.term) =
  fun projectee -> match projectee with | PP_State state_type -> state_type
let (compute_pre_type :
  Prims.bool ->
    FStarC_Reflection_Types.env ->
      FStarC_Reflection_Types.term ->
        (pre_post_type, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun dbg ->
    fun e ->
      fun pre ->
        let uu___ =
          FStar_InteractiveHelpers_Base.print_dbg dbg "[> compute_pre_type" in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range
                   "FStar.InteractiveHelpers.Effectful.fst"
                   (Prims.of_int (367)) (Prims.of_int (2))
                   (Prims.of_int (367)) (Prims.of_int (37)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range
                   "FStar.InteractiveHelpers.Effectful.fst"
                   (Prims.of_int (368)) (Prims.of_int (2))
                   (Prims.of_int (385)) (Prims.of_int (16)))))
          (Obj.magic uu___)
          (fun uu___1 ->
             (fun uu___1 ->
                let uu___2 =
                  FStar_InteractiveHelpers_ExploreTerm.safe_tc e pre in
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.InteractiveHelpers.Effectful.fst"
                              (Prims.of_int (368)) (Prims.of_int (8))
                              (Prims.of_int (368)) (Prims.of_int (21)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.InteractiveHelpers.Effectful.fst"
                              (Prims.of_int (368)) (Prims.of_int (2))
                              (Prims.of_int (385)) (Prims.of_int (16)))))
                     (Obj.magic uu___2)
                     (fun uu___3 ->
                        (fun uu___3 ->
                           match uu___3 with
                           | FStar_Pervasives_Native.None ->
                               let uu___4 =
                                 FStar_InteractiveHelpers_Base.print_dbg dbg
                                   "safe_tc failed" in
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.InteractiveHelpers.Effectful.fst"
                                             (Prims.of_int (370))
                                             (Prims.of_int (4))
                                             (Prims.of_int (370))
                                             (Prims.of_int (34)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.InteractiveHelpers.Effectful.fst"
                                             (Prims.of_int (371))
                                             (Prims.of_int (4))
                                             (Prims.of_int (371))
                                             (Prims.of_int (14)))))
                                    (Obj.magic uu___4)
                                    (fun uu___5 ->
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___6 -> PP_Unknown)))
                           | FStar_Pervasives_Native.Some ty ->
                               let uu___4 =
                                 FStar_InteractiveHelpers_Base.print_dbg dbg
                                   "safe_tc succeeded" in
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.InteractiveHelpers.Effectful.fst"
                                             (Prims.of_int (373))
                                             (Prims.of_int (4))
                                             (Prims.of_int (373))
                                             (Prims.of_int (37)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.InteractiveHelpers.Effectful.fst"
                                             (Prims.of_int (373))
                                             (Prims.of_int (38))
                                             (Prims.of_int (385))
                                             (Prims.of_int (16)))))
                                    (Obj.magic uu___4)
                                    (fun uu___5 ->
                                       (fun uu___5 ->
                                          let uu___6 =
                                            FStar_Tactics_V1_SyntaxHelpers.collect_arr_bs
                                              ty in
                                          Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "FStar.InteractiveHelpers.Effectful.fst"
                                                        (Prims.of_int (374))
                                                        (Prims.of_int (17))
                                                        (Prims.of_int (374))
                                                        (Prims.of_int (34)))))
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "FStar.InteractiveHelpers.Effectful.fst"
                                                        (Prims.of_int (373))
                                                        (Prims.of_int (38))
                                                        (Prims.of_int (385))
                                                        (Prims.of_int (16)))))
                                               (Obj.magic uu___6)
                                               (fun uu___7 ->
                                                  (fun uu___7 ->
                                                     match uu___7 with
                                                     | (brs, c) ->
                                                         let uu___8 =
                                                           FStar_InteractiveHelpers_Base.print_dbg
                                                             dbg
                                                             (Prims.strcat
                                                                "num binders: "
                                                                (Prims.string_of_int
                                                                   (FStar_List_Tot_Base.length
                                                                    brs))) in
                                                         Obj.magic
                                                           (FStar_Tactics_Effect.tac_bind
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (375))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (375))
                                                                    (Prims.of_int (73)))))
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (376))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (385))
                                                                    (Prims.of_int (16)))))
                                                              (Obj.magic
                                                                 uu___8)
                                                              (fun uu___9 ->
                                                                 (fun uu___9
                                                                    ->
                                                                    match 
                                                                    (brs,
                                                                    (FStar_InteractiveHelpers_ExploreTerm.is_total_or_gtotal
                                                                    c))
                                                                    with
                                                                    | 
                                                                    ([],
                                                                    true) ->
                                                                    let uu___10
                                                                    =
                                                                    FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    "PP_Pure" in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (378))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (378))
                                                                    (Prims.of_int (29)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (379))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (379))
                                                                    (Prims.of_int (13)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    PP_Pure)))
                                                                    | 
                                                                    (b::[],
                                                                    true) ->
                                                                    let uu___10
                                                                    =
                                                                    let uu___11
                                                                    =
                                                                    let uu___12
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.term_to_string
                                                                    (FStar_Reflection_V1_Derived.type_of_binder
                                                                    b) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (381))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (381))
                                                                    (Prims.of_int (70)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    Prims.strcat
                                                                    "PP_State "
                                                                    uu___13)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (381))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (381))
                                                                    (Prims.of_int (71)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (381))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (381))
                                                                    (Prims.of_int (71)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    uu___12))
                                                                    uu___12) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (381))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (381))
                                                                    (Prims.of_int (71)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (382))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (382))
                                                                    (Prims.of_int (33)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    PP_State
                                                                    (FStar_Reflection_V1_Derived.type_of_binder
                                                                    b))))
                                                                    | 
                                                                    uu___10
                                                                    ->
                                                                    let uu___11
                                                                    =
                                                                    FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    "PP_Unknown" in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (384))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (384))
                                                                    (Prims.of_int (32)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (385))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (385))
                                                                    (Prims.of_int (16)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    PP_Unknown))))
                                                                   uu___9)))
                                                    uu___7))) uu___5)))
                          uu___3))) uu___1)
let (opt_remove_refin :
  FStarC_Reflection_Types.typ ->
    (FStarC_Reflection_Types.typ, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun ty ->
    let uu___ = FStarC_Tactics_V1_Builtins.inspect ty in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.InteractiveHelpers.Effectful.fst"
               (Prims.of_int (389)) (Prims.of_int (8)) (Prims.of_int (389))
               (Prims.of_int (18)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.InteractiveHelpers.Effectful.fst"
               (Prims.of_int (389)) (Prims.of_int (2)) (Prims.of_int (391))
               (Prims.of_int (11))))) (Obj.magic uu___)
      (fun uu___1 ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___2 ->
              match uu___1 with
              | FStarC_Reflection_V1_Data.Tv_Refine (uu___3, sort, uu___4) ->
                  sort
              | uu___3 -> ty))
let (compute_post_type :
  Prims.bool ->
    FStarC_Reflection_Types.env ->
      FStarC_Reflection_Types.term ->
        FStarC_Reflection_Types.term ->
          (pre_post_type, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun dbg ->
    fun e ->
      fun ret_type ->
        fun post ->
          let uu___ =
            FStar_InteractiveHelpers_Base.print_dbg dbg
              "[> compute_post_type" in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range
                     "FStar.InteractiveHelpers.Effectful.fst"
                     (Prims.of_int (395)) (Prims.of_int (2))
                     (Prims.of_int (395)) (Prims.of_int (38)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range
                     "FStar.InteractiveHelpers.Effectful.fst"
                     (Prims.of_int (395)) (Prims.of_int (39))
                     (Prims.of_int (443)) (Prims.of_int (16)))))
            (Obj.magic uu___)
            (fun uu___1 ->
               (fun uu___1 ->
                  let uu___2 =
                    Obj.magic
                      (FStar_Tactics_Effect.lift_div_tac
                         (fun uu___4 ->
                            fun uu___3 ->
                              (fun uu___3 ->
                                 fun c ->
                                   match FStar_InteractiveHelpers_ExploreTerm.get_total_or_gtotal_ret_type
                                           c
                                   with
                                   | FStar_Pervasives_Native.Some ret_ty ->
                                       Obj.magic
                                         (Obj.repr
                                            (let uu___4 =
                                               FStarC_Tactics_V1_Builtins.inspect
                                                 ret_ty in
                                             FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "FStar.InteractiveHelpers.Effectful.fst"
                                                        (Prims.of_int (398))
                                                        (Prims.of_int (26))
                                                        (Prims.of_int (398))
                                                        (Prims.of_int (42)))))
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "FStar.InteractiveHelpers.Effectful.fst"
                                                        (Prims.of_int (398))
                                                        (Prims.of_int (21))
                                                        (Prims.of_int (398))
                                                        (Prims.of_int (42)))))
                                               (Obj.magic uu___4)
                                               (fun uu___5 ->
                                                  FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___6 ->
                                                       FStar_Pervasives_Native.Some
                                                         uu___5))))
                                   | FStar_Pervasives_Native.None ->
                                       Obj.magic
                                         (Obj.repr
                                            (FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___4 ->
                                                  FStar_Pervasives_Native.None))))
                                uu___4 uu___3)) in
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.InteractiveHelpers.Effectful.fst"
                                (Prims.of_int (397)) (Prims.of_int (4))
                                (Prims.of_int (399)) (Prims.of_int (18)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.InteractiveHelpers.Effectful.fst"
                                (Prims.of_int (401)) (Prims.of_int (2))
                                (Prims.of_int (443)) (Prims.of_int (16)))))
                       (Obj.magic uu___2)
                       (fun uu___3 ->
                          (fun get_tot_ret_type ->
                             let uu___3 =
                               FStar_InteractiveHelpers_ExploreTerm.safe_tc e
                                 post in
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "FStar.InteractiveHelpers.Effectful.fst"
                                           (Prims.of_int (401))
                                           (Prims.of_int (8))
                                           (Prims.of_int (401))
                                           (Prims.of_int (22)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "FStar.InteractiveHelpers.Effectful.fst"
                                           (Prims.of_int (401))
                                           (Prims.of_int (2))
                                           (Prims.of_int (443))
                                           (Prims.of_int (16)))))
                                  (Obj.magic uu___3)
                                  (fun uu___4 ->
                                     (fun uu___4 ->
                                        match uu___4 with
                                        | FStar_Pervasives_Native.None ->
                                            let uu___5 =
                                              FStar_InteractiveHelpers_Base.print_dbg
                                                dbg "safe_tc failed" in
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "FStar.InteractiveHelpers.Effectful.fst"
                                                          (Prims.of_int (403))
                                                          (Prims.of_int (4))
                                                          (Prims.of_int (403))
                                                          (Prims.of_int (34)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "FStar.InteractiveHelpers.Effectful.fst"
                                                          (Prims.of_int (404))
                                                          (Prims.of_int (4))
                                                          (Prims.of_int (404))
                                                          (Prims.of_int (14)))))
                                                 (Obj.magic uu___5)
                                                 (fun uu___6 ->
                                                    FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___7 ->
                                                         PP_Unknown)))
                                        | FStar_Pervasives_Native.Some ty ->
                                            let uu___5 =
                                              FStar_InteractiveHelpers_Base.print_dbg
                                                dbg "safe_tc succeeded" in
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "FStar.InteractiveHelpers.Effectful.fst"
                                                          (Prims.of_int (406))
                                                          (Prims.of_int (4))
                                                          (Prims.of_int (406))
                                                          (Prims.of_int (37)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "FStar.InteractiveHelpers.Effectful.fst"
                                                          (Prims.of_int (406))
                                                          (Prims.of_int (38))
                                                          (Prims.of_int (443))
                                                          (Prims.of_int (16)))))
                                                 (Obj.magic uu___5)
                                                 (fun uu___6 ->
                                                    (fun uu___6 ->
                                                       let uu___7 =
                                                         FStar_Tactics_V1_SyntaxHelpers.collect_arr_bs
                                                           ty in
                                                       Obj.magic
                                                         (FStar_Tactics_Effect.tac_bind
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (407))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (407))
                                                                    (Prims.of_int (34)))))
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (406))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (443))
                                                                    (Prims.of_int (16)))))
                                                            (Obj.magic uu___7)
                                                            (fun uu___8 ->
                                                               (fun uu___8 ->
                                                                  match uu___8
                                                                  with
                                                                  | (brs, c)
                                                                    ->
                                                                    let uu___9
                                                                    =
                                                                    FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    (Prims.strcat
                                                                    "num binders: "
                                                                    (Prims.string_of_int
                                                                    (FStar_List_Tot_Base.length
                                                                    brs))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (408))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (408))
                                                                    (Prims.of_int (73)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (409))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (443))
                                                                    (Prims.of_int (16)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    match 
                                                                    (brs,
                                                                    (FStar_InteractiveHelpers_ExploreTerm.is_total_or_gtotal
                                                                    c))
                                                                    with
                                                                    | 
                                                                    (r::[],
                                                                    true) ->
                                                                    let uu___11
                                                                    =
                                                                    FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    "PP_Pure" in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (412))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (412))
                                                                    (Prims.of_int (29)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (413))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (413))
                                                                    (Prims.of_int (13)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    PP_Pure)))
                                                                    | 
                                                                    (s1::r::s2::[],
                                                                    true) ->
                                                                    let uu___11
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_Reflection_V1_Derived.type_of_binder
                                                                    r)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (416))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (416))
                                                                    (Prims.of_int (33)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (416))
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (440))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun r_ty
                                                                    ->
                                                                    let uu___12
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    FStar_Reflection_V1_Derived.type_of_binder
                                                                    s1)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (417))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (417))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (417))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (440))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (fun
                                                                    s1_ty ->
                                                                    let uu___13
                                                                    =
                                                                    opt_remove_refin
                                                                    (FStar_Reflection_V1_Derived.type_of_binder
                                                                    s2) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (421))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (421))
                                                                    (Prims.of_int (54)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (421))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (440))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    uu___13)
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    (fun
                                                                    s2_ty ->
                                                                    let uu___14
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    term_eq
                                                                    ret_type
                                                                    r_ty)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (422))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (422))
                                                                    (Prims.of_int (45)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (422))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (440))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    uu___14)
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    (fun
                                                                    ret_type_eq
                                                                    ->
                                                                    let uu___15
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    term_eq
                                                                    s1_ty
                                                                    s2_ty)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (423))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (423))
                                                                    (Prims.of_int (45)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (424))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (440))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    uu___15)
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    (fun
                                                                    state_type_eq
                                                                    ->
                                                                    let uu___16
                                                                    =
                                                                    let uu___17
                                                                    =
                                                                    let uu___18
                                                                    =
                                                                    let uu___19
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.term_to_string
                                                                    ret_type in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (424))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (424))
                                                                    (Prims.of_int (73)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (424))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (425))
                                                                    (Prims.of_int (58)))))
                                                                    (Obj.magic
                                                                    uu___19)
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    let uu___21
                                                                    =
                                                                    let uu___22
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.term_to_string
                                                                    r_ty in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (425))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (425))
                                                                    (Prims.of_int (58)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
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
                                                                    "\n-- binder: "
                                                                    uu___23)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (425))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (425))
                                                                    (Prims.of_int (58)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
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
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (424))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (425))
                                                                    (Prims.of_int (58)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___18)
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    Prims.strcat
                                                                    "- ret type:\n-- target: "
                                                                    uu___19)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (424))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (425))
                                                                    (Prims.of_int (59)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (424))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (425))
                                                                    (Prims.of_int (59)))))
                                                                    (Obj.magic
                                                                    uu___17)
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    uu___18))
                                                                    uu___18) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (424))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (425))
                                                                    (Prims.of_int (59)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (426))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (440))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    uu___16)
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    let uu___18
                                                                    =
                                                                    let uu___19
                                                                    =
                                                                    let uu___20
                                                                    =
                                                                    let uu___21
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.term_to_string
                                                                    s1_ty in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (426))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (426))
                                                                    (Prims.of_int (74)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (426))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (427))
                                                                    (Prims.of_int (60)))))
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
                                                                    FStarC_Tactics_V1_Builtins.term_to_string
                                                                    s2_ty in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (427))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (427))
                                                                    (Prims.of_int (60)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
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
                                                                    "\n-- binder2: "
                                                                    uu___25)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (427))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (427))
                                                                    (Prims.of_int (60)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
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
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (426))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (427))
                                                                    (Prims.of_int (60)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
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
                                                                    "- state types:\n-- binder1: "
                                                                    uu___21)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (426))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (427))
                                                                    (Prims.of_int (61)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (426))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (427))
                                                                    (Prims.of_int (61)))))
                                                                    (Obj.magic
                                                                    uu___19)
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    uu___20))
                                                                    uu___20) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (426))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (427))
                                                                    (Prims.of_int (61)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (428))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (440))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    uu___18)
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    let uu___20
                                                                    =
                                                                    FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    (Prims.strcat
                                                                    "- ret type equality: "
                                                                    (Prims.string_of_bool
                                                                    ret_type_eq)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (428))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (428))
                                                                    (Prims.of_int (74)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (429))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (440))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    uu___20)
                                                                    (fun
                                                                    uu___21
                                                                    ->
                                                                    (fun
                                                                    uu___21
                                                                    ->
                                                                    let uu___22
                                                                    =
                                                                    FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    (Prims.strcat
                                                                    "- state types equality: "
                                                                    (Prims.string_of_bool
                                                                    state_type_eq)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (429))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (429))
                                                                    (Prims.of_int (79)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (430))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (440))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    uu___22)
                                                                    (fun
                                                                    uu___23
                                                                    ->
                                                                    (fun
                                                                    uu___23
                                                                    ->
                                                                    if
                                                                    ret_type_eq
                                                                    &&
                                                                    state_type_eq
                                                                    then
                                                                    let uu___24
                                                                    =
                                                                    let uu___25
                                                                    =
                                                                    let uu___26
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.term_to_string
                                                                    (FStar_Reflection_V1_Derived.type_of_binder
                                                                    s1) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (433))
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (433))
                                                                    (Prims.of_int (70)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
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
                                                                    "PP_State"
                                                                    uu___27)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (433))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (433))
                                                                    (Prims.of_int (71)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (433))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (433))
                                                                    (Prims.of_int (71)))))
                                                                    (Obj.magic
                                                                    uu___25)
                                                                    (fun
                                                                    uu___26
                                                                    ->
                                                                    (fun
                                                                    uu___26
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    uu___26))
                                                                    uu___26) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (433))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (433))
                                                                    (Prims.of_int (71)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (434))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (434))
                                                                    (Prims.of_int (36)))))
                                                                    (Obj.magic
                                                                    uu___24)
                                                                    (fun
                                                                    uu___25
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___26
                                                                    ->
                                                                    PP_State
                                                                    (FStar_Reflection_V1_Derived.type_of_binder
                                                                    s1))))
                                                                    else
                                                                    (let uu___25
                                                                    =
                                                                    FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    "PP_Unknown" in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (438))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (438))
                                                                    (Prims.of_int (34)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (439))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (439))
                                                                    (Prims.of_int (18)))))
                                                                    (Obj.magic
                                                                    uu___25)
                                                                    (fun
                                                                    uu___26
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___27
                                                                    ->
                                                                    PP_Unknown)))))
                                                                    uu___23)))
                                                                    uu___21)))
                                                                    uu___19)))
                                                                    uu___17)))
                                                                    uu___16)))
                                                                    uu___15)))
                                                                    uu___14)))
                                                                    uu___13)))
                                                                    uu___12))
                                                                    | 
                                                                    uu___11
                                                                    ->
                                                                    let uu___12
                                                                    =
                                                                    FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    "PP_Unknown" in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (442))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (442))
                                                                    (Prims.of_int (32)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (443))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (443))
                                                                    (Prims.of_int (16)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    PP_Unknown))))
                                                                    uu___10)))
                                                                 uu___8)))
                                                      uu___6))) uu___4)))
                            uu___3))) uu___1)
let (check_pre_post_type :
  Prims.bool ->
    FStarC_Reflection_Types.env ->
      FStarC_Reflection_Types.term ->
        FStarC_Reflection_Types.term ->
          FStarC_Reflection_Types.term ->
            (pre_post_type, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun dbg ->
    fun e ->
      fun pre ->
        fun ret_type ->
          fun post ->
            let uu___ =
              FStar_InteractiveHelpers_Base.print_dbg dbg
                "[> check_pre_post_type" in
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range
                       "FStar.InteractiveHelpers.Effectful.fst"
                       (Prims.of_int (447)) (Prims.of_int (2))
                       (Prims.of_int (447)) (Prims.of_int (40)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range
                       "FStar.InteractiveHelpers.Effectful.fst"
                       (Prims.of_int (448)) (Prims.of_int (2))
                       (Prims.of_int (457)) (Prims.of_int (14)))))
              (Obj.magic uu___)
              (fun uu___1 ->
                 (fun uu___1 ->
                    let uu___2 =
                      let uu___3 = compute_pre_type dbg e pre in
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.InteractiveHelpers.Effectful.fst"
                                 (Prims.of_int (448)) (Prims.of_int (8))
                                 (Prims.of_int (448)) (Prims.of_int (34)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.InteractiveHelpers.Effectful.fst"
                                 (Prims.of_int (448)) (Prims.of_int (8))
                                 (Prims.of_int (448)) (Prims.of_int (73)))))
                        (Obj.magic uu___3)
                        (fun uu___4 ->
                           (fun uu___4 ->
                              let uu___5 =
                                compute_post_type dbg e ret_type post in
                              Obj.magic
                                (FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "FStar.InteractiveHelpers.Effectful.fst"
                                            (Prims.of_int (448))
                                            (Prims.of_int (36))
                                            (Prims.of_int (448))
                                            (Prims.of_int (73)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "FStar.InteractiveHelpers.Effectful.fst"
                                            (Prims.of_int (448))
                                            (Prims.of_int (8))
                                            (Prims.of_int (448))
                                            (Prims.of_int (73)))))
                                   (Obj.magic uu___5)
                                   (fun uu___6 ->
                                      FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___7 -> (uu___4, uu___6)))))
                             uu___4) in
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.InteractiveHelpers.Effectful.fst"
                                  (Prims.of_int (448)) (Prims.of_int (8))
                                  (Prims.of_int (448)) (Prims.of_int (73)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.InteractiveHelpers.Effectful.fst"
                                  (Prims.of_int (448)) (Prims.of_int (2))
                                  (Prims.of_int (457)) (Prims.of_int (14)))))
                         (Obj.magic uu___2)
                         (fun uu___3 ->
                            (fun uu___3 ->
                               match uu___3 with
                               | (PP_Pure, PP_Pure) ->
                                   let uu___4 =
                                     FStar_InteractiveHelpers_Base.print_dbg
                                       dbg "PP_Pure, PP_Pure" in
                                   Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "FStar.InteractiveHelpers.Effectful.fst"
                                                 (Prims.of_int (450))
                                                 (Prims.of_int (4))
                                                 (Prims.of_int (450))
                                                 (Prims.of_int (36)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "FStar.InteractiveHelpers.Effectful.fst"
                                                 (Prims.of_int (451))
                                                 (Prims.of_int (4))
                                                 (Prims.of_int (451))
                                                 (Prims.of_int (11)))))
                                        (Obj.magic uu___4)
                                        (fun uu___5 ->
                                           FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___6 -> PP_Pure)))
                               | (PP_State ty1, PP_State ty2) ->
                                   let uu___4 =
                                     FStar_InteractiveHelpers_Base.print_dbg
                                       dbg "PP_State, PP_State" in
                                   Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "FStar.InteractiveHelpers.Effectful.fst"
                                                 (Prims.of_int (453))
                                                 (Prims.of_int (4))
                                                 (Prims.of_int (453))
                                                 (Prims.of_int (38)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "FStar.InteractiveHelpers.Effectful.fst"
                                                 (Prims.of_int (454))
                                                 (Prims.of_int (4))
                                                 (Prims.of_int (454))
                                                 (Prims.of_int (56)))))
                                        (Obj.magic uu___4)
                                        (fun uu___5 ->
                                           FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___6 ->
                                                if term_eq ty1 ty2
                                                then PP_State ty1
                                                else PP_Unknown)))
                               | uu___4 ->
                                   let uu___5 =
                                     FStar_InteractiveHelpers_Base.print_dbg
                                       dbg "_, _" in
                                   Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "FStar.InteractiveHelpers.Effectful.fst"
                                                 (Prims.of_int (456))
                                                 (Prims.of_int (4))
                                                 (Prims.of_int (456))
                                                 (Prims.of_int (24)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "FStar.InteractiveHelpers.Effectful.fst"
                                                 (Prims.of_int (457))
                                                 (Prims.of_int (4))
                                                 (Prims.of_int (457))
                                                 (Prims.of_int (14)))))
                                        (Obj.magic uu___5)
                                        (fun uu___6 ->
                                           FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___7 -> PP_Unknown))))
                              uu___3))) uu___1)
let (check_opt_pre_post_type :
  Prims.bool ->
    FStarC_Reflection_Types.env ->
      FStarC_Reflection_Types.term FStar_Pervasives_Native.option ->
        FStarC_Reflection_Types.term ->
          FStarC_Reflection_Types.term FStar_Pervasives_Native.option ->
            (pre_post_type FStar_Pervasives_Native.option, unit)
              FStar_Tactics_Effect.tac_repr)
  =
  fun dbg ->
    fun e ->
      fun opt_pre ->
        fun ret_type ->
          fun opt_post ->
            let uu___ =
              FStar_InteractiveHelpers_Base.print_dbg dbg
                "[> check_opt_pre_post_type" in
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range
                       "FStar.InteractiveHelpers.Effectful.fst"
                       (Prims.of_int (461)) (Prims.of_int (2))
                       (Prims.of_int (461)) (Prims.of_int (44)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range
                       "FStar.InteractiveHelpers.Effectful.fst"
                       (Prims.of_int (462)) (Prims.of_int (2))
                       (Prims.of_int (474)) (Prims.of_int (8)))))
              (Obj.magic uu___)
              (fun uu___1 ->
                 (fun uu___1 ->
                    match (opt_pre, opt_post) with
                    | (FStar_Pervasives_Native.Some pre,
                       FStar_Pervasives_Native.Some post) ->
                        let uu___2 =
                          FStar_InteractiveHelpers_Base.print_dbg dbg
                            "Some pre, Some post" in
                        Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "FStar.InteractiveHelpers.Effectful.fst"
                                      (Prims.of_int (464)) (Prims.of_int (4))
                                      (Prims.of_int (464))
                                      (Prims.of_int (39)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "FStar.InteractiveHelpers.Effectful.fst"
                                      (Prims.of_int (465)) (Prims.of_int (4))
                                      (Prims.of_int (465))
                                      (Prims.of_int (54)))))
                             (Obj.magic uu___2)
                             (fun uu___3 ->
                                (fun uu___3 ->
                                   let uu___4 =
                                     check_pre_post_type dbg e pre ret_type
                                       post in
                                   Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "FStar.InteractiveHelpers.Effectful.fst"
                                                 (Prims.of_int (465))
                                                 (Prims.of_int (9))
                                                 (Prims.of_int (465))
                                                 (Prims.of_int (54)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "FStar.InteractiveHelpers.Effectful.fst"
                                                 (Prims.of_int (465))
                                                 (Prims.of_int (4))
                                                 (Prims.of_int (465))
                                                 (Prims.of_int (54)))))
                                        (Obj.magic uu___4)
                                        (fun uu___5 ->
                                           FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___6 ->
                                                FStar_Pervasives_Native.Some
                                                  uu___5)))) uu___3))
                    | (FStar_Pervasives_Native.Some pre,
                       FStar_Pervasives_Native.None) ->
                        let uu___2 =
                          FStar_InteractiveHelpers_Base.print_dbg dbg
                            "Some pre, None" in
                        Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "FStar.InteractiveHelpers.Effectful.fst"
                                      (Prims.of_int (467)) (Prims.of_int (4))
                                      (Prims.of_int (467))
                                      (Prims.of_int (34)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "FStar.InteractiveHelpers.Effectful.fst"
                                      (Prims.of_int (468)) (Prims.of_int (4))
                                      (Prims.of_int (468))
                                      (Prims.of_int (37)))))
                             (Obj.magic uu___2)
                             (fun uu___3 ->
                                (fun uu___3 ->
                                   let uu___4 = compute_pre_type dbg e pre in
                                   Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "FStar.InteractiveHelpers.Effectful.fst"
                                                 (Prims.of_int (468))
                                                 (Prims.of_int (9))
                                                 (Prims.of_int (468))
                                                 (Prims.of_int (37)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "FStar.InteractiveHelpers.Effectful.fst"
                                                 (Prims.of_int (468))
                                                 (Prims.of_int (4))
                                                 (Prims.of_int (468))
                                                 (Prims.of_int (37)))))
                                        (Obj.magic uu___4)
                                        (fun uu___5 ->
                                           FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___6 ->
                                                FStar_Pervasives_Native.Some
                                                  uu___5)))) uu___3))
                    | (FStar_Pervasives_Native.None,
                       FStar_Pervasives_Native.Some post) ->
                        let uu___2 =
                          FStar_InteractiveHelpers_Base.print_dbg dbg
                            "None, Some post" in
                        Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "FStar.InteractiveHelpers.Effectful.fst"
                                      (Prims.of_int (470)) (Prims.of_int (4))
                                      (Prims.of_int (470))
                                      (Prims.of_int (35)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "FStar.InteractiveHelpers.Effectful.fst"
                                      (Prims.of_int (471)) (Prims.of_int (4))
                                      (Prims.of_int (471))
                                      (Prims.of_int (48)))))
                             (Obj.magic uu___2)
                             (fun uu___3 ->
                                (fun uu___3 ->
                                   let uu___4 =
                                     compute_post_type dbg e ret_type post in
                                   Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "FStar.InteractiveHelpers.Effectful.fst"
                                                 (Prims.of_int (471))
                                                 (Prims.of_int (9))
                                                 (Prims.of_int (471))
                                                 (Prims.of_int (48)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "FStar.InteractiveHelpers.Effectful.fst"
                                                 (Prims.of_int (471))
                                                 (Prims.of_int (4))
                                                 (Prims.of_int (471))
                                                 (Prims.of_int (48)))))
                                        (Obj.magic uu___4)
                                        (fun uu___5 ->
                                           FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___6 ->
                                                FStar_Pervasives_Native.Some
                                                  uu___5)))) uu___3))
                    | (FStar_Pervasives_Native.None,
                       FStar_Pervasives_Native.None) ->
                        let uu___2 =
                          FStar_InteractiveHelpers_Base.print_dbg dbg
                            "None, None" in
                        Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "FStar.InteractiveHelpers.Effectful.fst"
                                      (Prims.of_int (473)) (Prims.of_int (4))
                                      (Prims.of_int (473))
                                      (Prims.of_int (30)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "FStar.InteractiveHelpers.Effectful.fst"
                                      (Prims.of_int (474)) (Prims.of_int (4))
                                      (Prims.of_int (474)) (Prims.of_int (8)))))
                             (Obj.magic uu___2)
                             (fun uu___3 ->
                                FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___4 -> FStar_Pervasives_Native.None))))
                   uu___1)
let rec (_introduce_variables_for_abs :
  FStar_InteractiveHelpers_Base.genv ->
    FStarC_Reflection_Types.typ ->
      ((FStarC_Reflection_Types.term Prims.list *
         FStarC_Reflection_Types.binder Prims.list *
         FStar_InteractiveHelpers_Base.genv),
        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun ge ->
    fun ty ->
      let uu___ = FStarC_Tactics_V1_Builtins.inspect ty in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.InteractiveHelpers.Effectful.fst"
                 (Prims.of_int (478)) (Prims.of_int (8)) (Prims.of_int (478))
                 (Prims.of_int (18)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.InteractiveHelpers.Effectful.fst"
                 (Prims.of_int (478)) (Prims.of_int (2)) (Prims.of_int (489))
                 (Prims.of_int (18))))) (Obj.magic uu___)
        (fun uu___1 ->
           (fun uu___1 ->
              match uu___1 with
              | FStarC_Reflection_V1_Data.Tv_Arrow (b, c) ->
                  Obj.magic
                    (Obj.repr
                       (let uu___2 =
                          let uu___3 =
                            let uu___4 =
                              FStar_Tactics_V1_Derived.name_of_binder b in
                            FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "FStar.InteractiveHelpers.Effectful.fst"
                                       (Prims.of_int (480))
                                       (Prims.of_int (52))
                                       (Prims.of_int (480))
                                       (Prims.of_int (68)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range "Prims.fst"
                                       (Prims.of_int (611))
                                       (Prims.of_int (19))
                                       (Prims.of_int (611))
                                       (Prims.of_int (31)))))
                              (Obj.magic uu___4)
                              (fun uu___5 ->
                                 FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___6 -> Prims.strcat "__" uu___5)) in
                          FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.InteractiveHelpers.Effectful.fst"
                                     (Prims.of_int (480)) (Prims.of_int (44))
                                     (Prims.of_int (480)) (Prims.of_int (69)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.InteractiveHelpers.Effectful.fst"
                                     (Prims.of_int (480)) (Prims.of_int (18))
                                     (Prims.of_int (480)) (Prims.of_int (88)))))
                            (Obj.magic uu___3)
                            (fun uu___4 ->
                               (fun uu___4 ->
                                  Obj.magic
                                    (FStar_InteractiveHelpers_Base.genv_push_fresh_binder
                                       ge uu___4
                                       (FStar_Reflection_V1_Derived.type_of_binder
                                          b))) uu___4) in
                        FStar_Tactics_Effect.tac_bind
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "FStar.InteractiveHelpers.Effectful.fst"
                                   (Prims.of_int (480)) (Prims.of_int (18))
                                   (Prims.of_int (480)) (Prims.of_int (88)))))
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "FStar.InteractiveHelpers.Effectful.fst"
                                   (Prims.of_int (479)) (Prims.of_int (19))
                                   (Prims.of_int (488)) (Prims.of_int (7)))))
                          (Obj.magic uu___2)
                          (fun uu___3 ->
                             (fun uu___3 ->
                                match uu___3 with
                                | (ge1, b1) ->
                                    let uu___4 =
                                      Obj.magic
                                        (FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___5 ->
                                              FStar_Reflection_V1_Derived.bv_of_binder
                                                b1)) in
                                    Obj.magic
                                      (FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "FStar.InteractiveHelpers.Effectful.fst"
                                                  (Prims.of_int (481))
                                                  (Prims.of_int (14))
                                                  (Prims.of_int (481))
                                                  (Prims.of_int (29)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "FStar.InteractiveHelpers.Effectful.fst"
                                                  (Prims.of_int (481))
                                                  (Prims.of_int (32))
                                                  (Prims.of_int (488))
                                                  (Prims.of_int (7)))))
                                         (Obj.magic uu___4)
                                         (fun uu___5 ->
                                            (fun bv1 ->
                                               let uu___5 =
                                                 FStarC_Tactics_V1_Builtins.pack
                                                   (FStarC_Reflection_V1_Data.Tv_Var
                                                      bv1) in
                                               Obj.magic
                                                 (FStar_Tactics_Effect.tac_bind
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "FStar.InteractiveHelpers.Effectful.fst"
                                                             (Prims.of_int (482))
                                                             (Prims.of_int (13))
                                                             (Prims.of_int (482))
                                                             (Prims.of_int (30)))))
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "FStar.InteractiveHelpers.Effectful.fst"
                                                             (Prims.of_int (483))
                                                             (Prims.of_int (10))
                                                             (Prims.of_int (487))
                                                             (Prims.of_int (29)))))
                                                    (Obj.magic uu___5)
                                                    (fun uu___6 ->
                                                       (fun v1 ->
                                                          match FStar_InteractiveHelpers_ExploreTerm.get_total_or_gtotal_ret_type
                                                                  c
                                                          with
                                                          | FStar_Pervasives_Native.Some
                                                              ty1 ->
                                                              Obj.magic
                                                                (Obj.repr
                                                                   (let uu___6
                                                                    =
                                                                    _introduce_variables_for_abs
                                                                    ge1 ty1 in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (485))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (485))
                                                                    (Prims.of_int (60)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (484))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (486))
                                                                    (Prims.of_int (29)))))
                                                                    (Obj.magic
                                                                    uu___6)
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    match uu___7
                                                                    with
                                                                    | 
                                                                    (vl, bl,
                                                                    ge2) ->
                                                                    ((v1 ::
                                                                    vl), (b1
                                                                    :: bl),
                                                                    ge2)))))
                                                          | FStar_Pervasives_Native.None
                                                              ->
                                                              Obj.magic
                                                                (Obj.repr
                                                                   (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    ([v1],
                                                                    [b1],
                                                                    ge1)))))
                                                         uu___6))) uu___5)))
                               uu___3)))
              | uu___2 ->
                  Obj.magic
                    (Obj.repr
                       (FStar_Tactics_Effect.lift_div_tac
                          (fun uu___3 -> ([], [], ge))))) uu___1)
let (introduce_variables_for_abs :
  FStar_InteractiveHelpers_Base.genv ->
    FStarC_Reflection_Types.term ->
      ((FStarC_Reflection_Types.term Prims.list *
         FStarC_Reflection_Types.binder Prims.list *
         FStar_InteractiveHelpers_Base.genv),
        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun ge ->
    fun tm ->
      let uu___ =
        FStar_InteractiveHelpers_ExploreTerm.safe_tc
          ge.FStar_InteractiveHelpers_Base.env tm in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.InteractiveHelpers.Effectful.fst"
                 (Prims.of_int (493)) (Prims.of_int (8)) (Prims.of_int (493))
                 (Prims.of_int (25)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.InteractiveHelpers.Effectful.fst"
                 (Prims.of_int (493)) (Prims.of_int (2)) (Prims.of_int (495))
                 (Prims.of_int (22))))) (Obj.magic uu___)
        (fun uu___1 ->
           (fun uu___1 ->
              match uu___1 with
              | FStar_Pervasives_Native.Some ty ->
                  Obj.magic (Obj.repr (_introduce_variables_for_abs ge ty))
              | FStar_Pervasives_Native.None ->
                  Obj.magic
                    (Obj.repr
                       (FStar_Tactics_Effect.lift_div_tac
                          (fun uu___2 -> ([], [], ge))))) uu___1)
let (introduce_variables_for_opt_abs :
  FStar_InteractiveHelpers_Base.genv ->
    FStarC_Reflection_Types.term FStar_Pervasives_Native.option ->
      ((FStarC_Reflection_Types.term Prims.list *
         FStarC_Reflection_Types.binder Prims.list *
         FStar_InteractiveHelpers_Base.genv),
        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun ge ->
         fun opt_tm ->
           match opt_tm with
           | FStar_Pervasives_Native.Some tm ->
               Obj.magic (Obj.repr (introduce_variables_for_abs ge tm))
           | FStar_Pervasives_Native.None ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac
                       (fun uu___ -> ([], [], ge))))) uu___1 uu___
let (effect_type_is_stateful :
  FStar_InteractiveHelpers_ExploreTerm.effect_type -> Prims.bool) =
  fun etype ->
    match etype with
    | FStar_InteractiveHelpers_ExploreTerm.E_Total -> false
    | FStar_InteractiveHelpers_ExploreTerm.E_GTotal -> false
    | FStar_InteractiveHelpers_ExploreTerm.E_Lemma -> false
    | FStar_InteractiveHelpers_ExploreTerm.E_PURE -> false
    | FStar_InteractiveHelpers_ExploreTerm.E_Pure -> false
    | FStar_InteractiveHelpers_ExploreTerm.E_Stack -> true
    | FStar_InteractiveHelpers_ExploreTerm.E_ST -> true
    | FStar_InteractiveHelpers_ExploreTerm.E_Unknown -> true
let (is_st_get :
  Prims.bool ->
    FStarC_Reflection_Types.term ->
      (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun dbg ->
    fun t ->
      let uu___ =
        let uu___1 =
          let uu___2 = FStarC_Tactics_V1_Builtins.term_to_string t in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range
                     "FStar.InteractiveHelpers.Effectful.fst"
                     (Prims.of_int (511)) (Prims.of_int (37))
                     (Prims.of_int (511)) (Prims.of_int (53)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Prims.fst" (Prims.of_int (611))
                     (Prims.of_int (19)) (Prims.of_int (611))
                     (Prims.of_int (31))))) (Obj.magic uu___2)
            (fun uu___3 ->
               FStar_Tactics_Effect.lift_div_tac
                 (fun uu___4 -> Prims.strcat "[> is_st_get:\n" uu___3)) in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range
                   "FStar.InteractiveHelpers.Effectful.fst"
                   (Prims.of_int (511)) (Prims.of_int (16))
                   (Prims.of_int (511)) (Prims.of_int (54)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range
                   "FStar.InteractiveHelpers.Effectful.fst"
                   (Prims.of_int (511)) (Prims.of_int (2))
                   (Prims.of_int (511)) (Prims.of_int (54)))))
          (Obj.magic uu___1)
          (fun uu___2 ->
             (fun uu___2 ->
                Obj.magic
                  (FStar_InteractiveHelpers_Base.print_dbg dbg uu___2))
               uu___2) in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.InteractiveHelpers.Effectful.fst"
                 (Prims.of_int (511)) (Prims.of_int (2)) (Prims.of_int (511))
                 (Prims.of_int (54)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.InteractiveHelpers.Effectful.fst"
                 (Prims.of_int (512)) (Prims.of_int (2)) (Prims.of_int (525))
                 (Prims.of_int (9))))) (Obj.magic uu___)
        (fun uu___1 ->
           (fun uu___1 ->
              let uu___2 = FStarC_Tactics_V1_Builtins.inspect t in
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.InteractiveHelpers.Effectful.fst"
                            (Prims.of_int (512)) (Prims.of_int (8))
                            (Prims.of_int (512)) (Prims.of_int (17)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.InteractiveHelpers.Effectful.fst"
                            (Prims.of_int (512)) (Prims.of_int (2))
                            (Prims.of_int (525)) (Prims.of_int (9)))))
                   (Obj.magic uu___2)
                   (fun uu___3 ->
                      (fun uu___3 ->
                         match uu___3 with
                         | FStarC_Reflection_V1_Data.Tv_App (hd, (a, qual))
                             ->
                             let uu___4 =
                               FStar_InteractiveHelpers_Base.print_dbg dbg
                                 "-> Is Tv_App" in
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "FStar.InteractiveHelpers.Effectful.fst"
                                           (Prims.of_int (514))
                                           (Prims.of_int (4))
                                           (Prims.of_int (514))
                                           (Prims.of_int (32)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "FStar.InteractiveHelpers.Effectful.fst"
                                           (Prims.of_int (515))
                                           (Prims.of_int (10))
                                           (Prims.of_int (521))
                                           (Prims.of_int (11)))))
                                  (Obj.magic uu___4)
                                  (fun uu___5 ->
                                     (fun uu___5 ->
                                        let uu___6 =
                                          FStarC_Tactics_V1_Builtins.inspect
                                            hd in
                                        Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "FStar.InteractiveHelpers.Effectful.fst"
                                                      (Prims.of_int (515))
                                                      (Prims.of_int (16))
                                                      (Prims.of_int (515))
                                                      (Prims.of_int (26)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "FStar.InteractiveHelpers.Effectful.fst"
                                                      (Prims.of_int (515))
                                                      (Prims.of_int (10))
                                                      (Prims.of_int (521))
                                                      (Prims.of_int (11)))))
                                             (Obj.magic uu___6)
                                             (fun uu___7 ->
                                                (fun uu___7 ->
                                                   match uu___7 with
                                                   | FStarC_Reflection_V1_Data.Tv_FVar
                                                       fv ->
                                                       let uu___8 =
                                                         FStar_InteractiveHelpers_Base.print_dbg
                                                           dbg
                                                           (Prims.strcat
                                                              "-> Head is Tv_FVar: "
                                                              (FStar_Reflection_V1_Derived.fv_to_string
                                                                 fv)) in
                                                       Obj.magic
                                                         (FStar_Tactics_Effect.tac_bind
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (517))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (517))
                                                                    (Prims.of_int (62)))))
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (518))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (518))
                                                                    (Prims.of_int (56)))))
                                                            (Obj.magic uu___8)
                                                            (fun uu___9 ->
                                                               FStar_Tactics_Effect.lift_div_tac
                                                                 (fun uu___10
                                                                    ->
                                                                    FStar_InteractiveHelpers_Base.fv_eq_name
                                                                    fv
                                                                    ["FStar";
                                                                    "HyperStack";
                                                                    "ST";
                                                                    "get"])))
                                                   | uu___8 ->
                                                       let uu___9 =
                                                         FStar_InteractiveHelpers_Base.print_dbg
                                                           dbg
                                                           "-> Head is not Tv_FVar" in
                                                       Obj.magic
                                                         (FStar_Tactics_Effect.tac_bind
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (520))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (520))
                                                                    (Prims.of_int (44)))))
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (521))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (521))
                                                                    (Prims.of_int (11)))))
                                                            (Obj.magic uu___9)
                                                            (fun uu___10 ->
                                                               FStar_Tactics_Effect.lift_div_tac
                                                                 (fun uu___11
                                                                    -> false))))
                                                  uu___7))) uu___5))
                         | uu___4 ->
                             let uu___5 =
                               FStar_InteractiveHelpers_Base.print_dbg dbg
                                 "-> Is not Tv_App" in
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "FStar.InteractiveHelpers.Effectful.fst"
                                           (Prims.of_int (524))
                                           (Prims.of_int (4))
                                           (Prims.of_int (524))
                                           (Prims.of_int (36)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "FStar.InteractiveHelpers.Effectful.fst"
                                           (Prims.of_int (525))
                                           (Prims.of_int (4))
                                           (Prims.of_int (525))
                                           (Prims.of_int (9)))))
                                  (Obj.magic uu___5)
                                  (fun uu___6 ->
                                     FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___7 -> false)))) uu___3)))
             uu___1)
let (is_let_st_get :
  Prims.bool ->
    FStarC_Reflection_V1_Data.term_view ->
      ((FStarC_Reflection_Types.bv * FStarC_Reflection_Types.typ)
         FStar_Pervasives_Native.option,
        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun dbg ->
    fun t ->
      let uu___ =
        let uu___1 =
          let uu___2 =
            let uu___3 = FStarC_Tactics_V1_Builtins.pack t in
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range
                       "FStar.InteractiveHelpers.Effectful.fst"
                       (Prims.of_int (527)) (Prims.of_int (23))
                       (Prims.of_int (527)) (Prims.of_int (24)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range
                       "FStar.InteractiveHelpers.Effectful.fst"
                       (Prims.of_int (528)) (Prims.of_int (41))
                       (Prims.of_int (528)) (Prims.of_int (57)))))
              (Obj.magic uu___3)
              (fun uu___4 ->
                 (fun uu___4 ->
                    Obj.magic
                      (FStarC_Tactics_V1_Builtins.term_to_string uu___4))
                   uu___4) in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range
                     "FStar.InteractiveHelpers.Effectful.fst"
                     (Prims.of_int (528)) (Prims.of_int (41))
                     (Prims.of_int (528)) (Prims.of_int (57)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Prims.fst" (Prims.of_int (611))
                     (Prims.of_int (19)) (Prims.of_int (611))
                     (Prims.of_int (31))))) (Obj.magic uu___2)
            (fun uu___3 ->
               FStar_Tactics_Effect.lift_div_tac
                 (fun uu___4 -> Prims.strcat "[> is_let_st_get:\n" uu___3)) in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range
                   "FStar.InteractiveHelpers.Effectful.fst"
                   (Prims.of_int (528)) (Prims.of_int (16))
                   (Prims.of_int (528)) (Prims.of_int (58)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range
                   "FStar.InteractiveHelpers.Effectful.fst"
                   (Prims.of_int (528)) (Prims.of_int (2))
                   (Prims.of_int (528)) (Prims.of_int (58)))))
          (Obj.magic uu___1)
          (fun uu___2 ->
             (fun uu___2 ->
                Obj.magic
                  (FStar_InteractiveHelpers_Base.print_dbg dbg uu___2))
               uu___2) in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.InteractiveHelpers.Effectful.fst"
                 (Prims.of_int (528)) (Prims.of_int (2)) (Prims.of_int (528))
                 (Prims.of_int (58)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.InteractiveHelpers.Effectful.fst"
                 (Prims.of_int (529)) (Prims.of_int (2)) (Prims.of_int (535))
                 (Prims.of_int (8))))) (Obj.magic uu___)
        (fun uu___1 ->
           (fun uu___1 ->
              match t with
              | FStarC_Reflection_V1_Data.Tv_Let
                  (recf, attrs, bv, ty, def, body) ->
                  let uu___2 =
                    FStar_InteractiveHelpers_Base.print_dbg dbg
                      "The term is a let expression" in
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.InteractiveHelpers.Effectful.fst"
                                (Prims.of_int (531)) (Prims.of_int (4))
                                (Prims.of_int (531)) (Prims.of_int (48)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.InteractiveHelpers.Effectful.fst"
                                (Prims.of_int (532)) (Prims.of_int (4))
                                (Prims.of_int (532)) (Prims.of_int (53)))))
                       (Obj.magic uu___2)
                       (fun uu___3 ->
                          (fun uu___3 ->
                             let uu___4 = is_st_get dbg def in
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "FStar.InteractiveHelpers.Effectful.fst"
                                           (Prims.of_int (532))
                                           (Prims.of_int (7))
                                           (Prims.of_int (532))
                                           (Prims.of_int (24)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "FStar.InteractiveHelpers.Effectful.fst"
                                           (Prims.of_int (532))
                                           (Prims.of_int (4))
                                           (Prims.of_int (532))
                                           (Prims.of_int (53)))))
                                  (Obj.magic uu___4)
                                  (fun uu___5 ->
                                     FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___6 ->
                                          if uu___5
                                          then
                                            FStar_Pervasives_Native.Some
                                              (bv, ty)
                                          else FStar_Pervasives_Native.None))))
                            uu___3))
              | uu___2 ->
                  let uu___3 =
                    FStar_InteractiveHelpers_Base.print_dbg dbg
                      "The term is not a let expression" in
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.InteractiveHelpers.Effectful.fst"
                                (Prims.of_int (534)) (Prims.of_int (4))
                                (Prims.of_int (534)) (Prims.of_int (52)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.InteractiveHelpers.Effectful.fst"
                                (Prims.of_int (535)) (Prims.of_int (4))
                                (Prims.of_int (535)) (Prims.of_int (8)))))
                       (Obj.magic uu___3)
                       (fun uu___4 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___5 -> FStar_Pervasives_Native.None))))
             uu___1)
let (term_has_effectful_comp :
  Prims.bool ->
    FStarC_Reflection_Types.env ->
      FStarC_Reflection_Types.term ->
        (Prims.bool FStar_Pervasives_Native.option, unit)
          FStar_Tactics_Effect.tac_repr)
  =
  fun dbg ->
    fun e ->
      fun tm ->
        let uu___ =
          FStar_InteractiveHelpers_Base.print_dbg dbg
            "[> term_has_effectful_comp" in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range
                   "FStar.InteractiveHelpers.Effectful.fst"
                   (Prims.of_int (547)) (Prims.of_int (2))
                   (Prims.of_int (547)) (Prims.of_int (44)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range
                   "FStar.InteractiveHelpers.Effectful.fst"
                   (Prims.of_int (547)) (Prims.of_int (45))
                   (Prims.of_int (555)) (Prims.of_int (8)))))
          (Obj.magic uu___)
          (fun uu___1 ->
             (fun uu___1 ->
                let uu___2 = compute_effect_info dbg e tm in
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.InteractiveHelpers.Effectful.fst"
                              (Prims.of_int (548)) (Prims.of_int (18))
                              (Prims.of_int (548)) (Prims.of_int (46)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.InteractiveHelpers.Effectful.fst"
                              (Prims.of_int (549)) (Prims.of_int (2))
                              (Prims.of_int (555)) (Prims.of_int (8)))))
                     (Obj.magic uu___2)
                     (fun uu___3 ->
                        (fun einfo_opt ->
                           match einfo_opt with
                           | FStar_Pervasives_Native.Some einfo ->
                               let uu___3 =
                                 FStar_InteractiveHelpers_Base.print_dbg dbg
                                   (Prims.strcat "Effect type: "
                                      (FStar_InteractiveHelpers_ExploreTerm.effect_type_to_string
                                         einfo.ei_type)) in
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.InteractiveHelpers.Effectful.fst"
                                             (Prims.of_int (551))
                                             (Prims.of_int (4))
                                             (Prims.of_int (551))
                                             (Prims.of_int (73)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.InteractiveHelpers.Effectful.fst"
                                             (Prims.of_int (552))
                                             (Prims.of_int (4))
                                             (Prims.of_int (552))
                                             (Prims.of_int (50)))))
                                    (Obj.magic uu___3)
                                    (fun uu___4 ->
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___5 ->
                                            FStar_Pervasives_Native.Some
                                              (Prims.op_Negation
                                                 (FStar_InteractiveHelpers_ExploreTerm.effect_type_is_pure
                                                    einfo.ei_type)))))
                           | FStar_Pervasives_Native.None ->
                               let uu___3 =
                                 FStar_InteractiveHelpers_Base.print_dbg dbg
                                   "Could not compute effect info" in
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.InteractiveHelpers.Effectful.fst"
                                             (Prims.of_int (554))
                                             (Prims.of_int (4))
                                             (Prims.of_int (554))
                                             (Prims.of_int (49)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.InteractiveHelpers.Effectful.fst"
                                             (Prims.of_int (555))
                                             (Prims.of_int (4))
                                             (Prims.of_int (555))
                                             (Prims.of_int (8)))))
                                    (Obj.magic uu___3)
                                    (fun uu___4 ->
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___5 ->
                                            FStar_Pervasives_Native.None))))
                          uu___3))) uu___1)
let (related_term_is_effectul :
  Prims.bool ->
    FStar_InteractiveHelpers_Base.genv ->
      FStarC_Reflection_V1_Data.term_view ->
        (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun dbg ->
    fun ge ->
      fun tv ->
        let uu___ =
          Obj.magic
            (FStar_Tactics_Effect.lift_div_tac
               (fun uu___1 ->
                  fun tm ->
                    let uu___2 =
                      term_has_effectful_comp dbg
                        ge.FStar_InteractiveHelpers_Base.env tm in
                    FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range
                               "FStar.InteractiveHelpers.Effectful.fst"
                               (Prims.of_int (567)) (Prims.of_int (4))
                               (Prims.of_int (567)) (Prims.of_int (41)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range
                               "FStar.InteractiveHelpers.Effectful.fst"
                               (Prims.of_int (567)) (Prims.of_int (4))
                               (Prims.of_int (567)) (Prims.of_int (55)))))
                      (Obj.magic uu___2)
                      (fun uu___3 ->
                         FStar_Tactics_Effect.lift_div_tac
                           (fun uu___4 ->
                              uu___3 <> (FStar_Pervasives_Native.Some false))))) in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range
                   "FStar.InteractiveHelpers.Effectful.fst"
                   (Prims.of_int (567)) (Prims.of_int (4))
                   (Prims.of_int (567)) (Prims.of_int (55)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range
                   "FStar.InteractiveHelpers.Effectful.fst"
                   (Prims.of_int (569)) (Prims.of_int (2))
                   (Prims.of_int (591)) (Prims.of_int (45)))))
          (Obj.magic uu___)
          (fun uu___1 ->
             (fun is_effectful ->
                match tv with
                | FStarC_Reflection_V1_Data.Tv_Var uu___1 ->
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___2 -> false)))
                | FStarC_Reflection_V1_Data.Tv_BVar uu___1 ->
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___2 -> false)))
                | FStarC_Reflection_V1_Data.Tv_FVar uu___1 ->
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___2 -> false)))
                | FStarC_Reflection_V1_Data.Tv_App (hd, (a, qual)) ->
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___1 -> false)))
                | FStarC_Reflection_V1_Data.Tv_Abs (br, body) ->
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___1 -> false)))
                | FStarC_Reflection_V1_Data.Tv_Arrow (br, c0) ->
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___1 -> false)))
                | FStarC_Reflection_V1_Data.Tv_Type uu___1 ->
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___2 -> false)))
                | FStarC_Reflection_V1_Data.Tv_Refine (bv, sort, ref) ->
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___1 -> false)))
                | FStarC_Reflection_V1_Data.Tv_Const uu___1 ->
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___2 -> false)))
                | FStarC_Reflection_V1_Data.Tv_Uvar (uu___1, uu___2) ->
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___3 -> false)))
                | FStarC_Reflection_V1_Data.Tv_Let
                    (recf, attrs, bv, ty, def, body) ->
                    Obj.magic (Obj.repr (is_effectful def))
                | FStarC_Reflection_V1_Data.Tv_Match
                    (scrutinee, _ret_opt, branches) ->
                    Obj.magic (Obj.repr (is_effectful scrutinee))
                | FStarC_Reflection_V1_Data.Tv_AscribedT (e, ty, tac, uu___1)
                    ->
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___2 -> false)))
                | FStarC_Reflection_V1_Data.Tv_AscribedC (e, c, tac, uu___1)
                    ->
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___2 -> false)))
                | uu___1 ->
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___2 -> true)))) uu___1)
let rec (find_mem_in_related :
  Prims.bool ->
    FStar_InteractiveHelpers_Base.genv ->
      FStarC_Reflection_V1_Data.term_view Prims.list ->
        ((FStarC_Reflection_Types.bv * FStarC_Reflection_Types.typ)
           FStar_Pervasives_Native.option,
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun dbg ->
           fun ge ->
             fun tms ->
               match tms with
               | [] ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.lift_div_tac
                           (fun uu___ -> FStar_Pervasives_Native.None)))
               | tv::tms' ->
                   Obj.magic
                     (Obj.repr
                        (let uu___ =
                           let uu___1 =
                             let uu___2 =
                               let uu___3 =
                                 FStarC_Tactics_V1_Builtins.pack tv in
                               FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "FStar.InteractiveHelpers.Effectful.fst"
                                          (Prims.of_int (608))
                                          (Prims.of_int (4))
                                          (Prims.of_int (608))
                                          (Prims.of_int (6)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "FStar.InteractiveHelpers.Effectful.fst"
                                          (Prims.of_int (609))
                                          (Prims.of_int (49))
                                          (Prims.of_int (609))
                                          (Prims.of_int (66)))))
                                 (Obj.magic uu___3)
                                 (fun uu___4 ->
                                    (fun uu___4 ->
                                       Obj.magic
                                         (FStarC_Tactics_V1_Builtins.term_to_string
                                            uu___4)) uu___4) in
                             FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "FStar.InteractiveHelpers.Effectful.fst"
                                        (Prims.of_int (609))
                                        (Prims.of_int (49))
                                        (Prims.of_int (609))
                                        (Prims.of_int (66)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range "Prims.fst"
                                        (Prims.of_int (611))
                                        (Prims.of_int (19))
                                        (Prims.of_int (611))
                                        (Prims.of_int (31)))))
                               (Obj.magic uu___2)
                               (fun uu___3 ->
                                  FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___4 ->
                                       Prims.strcat
                                         "[> find_mem_in_related:\n" uu___3)) in
                           FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "FStar.InteractiveHelpers.Effectful.fst"
                                      (Prims.of_int (609))
                                      (Prims.of_int (18))
                                      (Prims.of_int (609))
                                      (Prims.of_int (67)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "FStar.InteractiveHelpers.Effectful.fst"
                                      (Prims.of_int (609)) (Prims.of_int (4))
                                      (Prims.of_int (609))
                                      (Prims.of_int (67)))))
                             (Obj.magic uu___1)
                             (fun uu___2 ->
                                (fun uu___2 ->
                                   Obj.magic
                                     (FStar_InteractiveHelpers_Base.print_dbg
                                        dbg uu___2)) uu___2) in
                         FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "FStar.InteractiveHelpers.Effectful.fst"
                                    (Prims.of_int (609)) (Prims.of_int (4))
                                    (Prims.of_int (609)) (Prims.of_int (67)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "FStar.InteractiveHelpers.Effectful.fst"
                                    (Prims.of_int (610)) (Prims.of_int (4))
                                    (Prims.of_int (626)) (Prims.of_int (11)))))
                           (Obj.magic uu___)
                           (fun uu___1 ->
                              (fun uu___1 ->
                                 let uu___2 = is_let_st_get dbg tv in
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "FStar.InteractiveHelpers.Effectful.fst"
                                               (Prims.of_int (610))
                                               (Prims.of_int (10))
                                               (Prims.of_int (610))
                                               (Prims.of_int (30)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "FStar.InteractiveHelpers.Effectful.fst"
                                               (Prims.of_int (610))
                                               (Prims.of_int (4))
                                               (Prims.of_int (626))
                                               (Prims.of_int (11)))))
                                      (Obj.magic uu___2)
                                      (fun uu___3 ->
                                         (fun uu___3 ->
                                            match uu___3 with
                                            | FStar_Pervasives_Native.Some
                                                bvt ->
                                                let uu___4 =
                                                  FStar_InteractiveHelpers_Base.print_dbg
                                                    dbg
                                                    "Term is of the form `let x = FStar.HyperStack.ST.get ()`: success" in
                                                Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "FStar.InteractiveHelpers.Effectful.fst"
                                                              (Prims.of_int (612))
                                                              (Prims.of_int (6))
                                                              (Prims.of_int (612))
                                                              (Prims.of_int (87)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "FStar.InteractiveHelpers.Effectful.fst"
                                                              (Prims.of_int (613))
                                                              (Prims.of_int (6))
                                                              (Prims.of_int (613))
                                                              (Prims.of_int (14)))))
                                                     (Obj.magic uu___4)
                                                     (fun uu___5 ->
                                                        FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___6 ->
                                                             FStar_Pervasives_Native.Some
                                                               bvt)))
                                            | FStar_Pervasives_Native.None ->
                                                let uu___4 =
                                                  FStar_InteractiveHelpers_Base.print_dbg
                                                    dbg
                                                    "Term is not of the form `let x = FStar.HyperStack.ST.get ()`: continuing" in
                                                Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "FStar.InteractiveHelpers.Effectful.fst"
                                                              (Prims.of_int (615))
                                                              (Prims.of_int (6))
                                                              (Prims.of_int (615))
                                                              (Prims.of_int (94)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "FStar.InteractiveHelpers.Effectful.fst"
                                                              (Prims.of_int (616))
                                                              (Prims.of_int (6))
                                                              (Prims.of_int (626))
                                                              (Prims.of_int (11)))))
                                                     (Obj.magic uu___4)
                                                     (fun uu___5 ->
                                                        (fun uu___5 ->
                                                           let uu___6 =
                                                             related_term_is_effectul
                                                               dbg ge tv in
                                                           Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (616))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (616))
                                                                    (Prims.of_int (43)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (616))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (626))
                                                                    (Prims.of_int (11)))))
                                                                (Obj.magic
                                                                   uu___6)
                                                                (fun uu___7
                                                                   ->
                                                                   (fun
                                                                    uu___7 ->
                                                                    if uu___7
                                                                    then
                                                                    let uu___8
                                                                    =
                                                                    FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    "Term is effectful: stopping here" in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (619))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (619))
                                                                    (Prims.of_int (56)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (620))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (620))
                                                                    (Prims.of_int (12)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Pervasives_Native.None)))
                                                                    else
                                                                    (let uu___9
                                                                    =
                                                                    FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    "Term is not effectful: continuing" in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (624))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (624))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (625))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (625))
                                                                    (Prims.of_int (39)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    Obj.magic
                                                                    (find_mem_in_related
                                                                    dbg ge
                                                                    tms'))
                                                                    uu___10))))
                                                                    uu___7)))
                                                          uu___5))) uu___3)))
                                uu___1)))) uu___2 uu___1 uu___
let rec (find_mem_in_children :
  Prims.bool ->
    FStar_InteractiveHelpers_Base.genv ->
      FStarC_Reflection_Types.term ->
        ((FStar_InteractiveHelpers_Base.genv * FStarC_Reflection_Types.bv
           FStar_Pervasives_Native.option),
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun dbg ->
    fun ge ->
      fun child ->
        let uu___ = FStarC_Tactics_V1_Builtins.inspect child in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range
                   "FStar.InteractiveHelpers.Effectful.fst"
                   (Prims.of_int (639)) (Prims.of_int (8))
                   (Prims.of_int (639)) (Prims.of_int (21)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range
                   "FStar.InteractiveHelpers.Effectful.fst"
                   (Prims.of_int (639)) (Prims.of_int (2))
                   (Prims.of_int (646)) (Prims.of_int (17)))))
          (Obj.magic uu___)
          (fun uu___1 ->
             (fun uu___1 ->
                match uu___1 with
                | FStarC_Reflection_V1_Data.Tv_Let
                    (recf, attrs, bv, ty, def, body) ->
                    Obj.magic
                      (Obj.repr
                         (let uu___2 = is_st_get dbg def in
                          FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.InteractiveHelpers.Effectful.fst"
                                     (Prims.of_int (641)) (Prims.of_int (7))
                                     (Prims.of_int (641)) (Prims.of_int (24)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.InteractiveHelpers.Effectful.fst"
                                     (Prims.of_int (641)) (Prims.of_int (4))
                                     (Prims.of_int (645)) (Prims.of_int (39)))))
                            (Obj.magic uu___2)
                            (fun uu___3 ->
                               (fun uu___3 ->
                                  if uu___3
                                  then
                                    Obj.magic
                                      (Obj.repr
                                         (FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___4 ->
                                               (ge,
                                                 (FStar_Pervasives_Native.Some
                                                    bv)))))
                                  else
                                    Obj.magic
                                      (Obj.repr
                                         (let uu___5 =
                                            let uu___6 =
                                              term_has_effectful_comp dbg
                                                ge.FStar_InteractiveHelpers_Base.env
                                                def in
                                            FStar_Tactics_Effect.tac_bind
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "FStar.InteractiveHelpers.Effectful.fst"
                                                       (Prims.of_int (642))
                                                       (Prims.of_int (12))
                                                       (Prims.of_int (642))
                                                       (Prims.of_int (50)))))
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "FStar.InteractiveHelpers.Effectful.fst"
                                                       (Prims.of_int (642))
                                                       (Prims.of_int (12))
                                                       (Prims.of_int (642))
                                                       (Prims.of_int (64)))))
                                              (Obj.magic uu___6)
                                              (fun uu___7 ->
                                                 FStar_Tactics_Effect.lift_div_tac
                                                   (fun uu___8 ->
                                                      uu___7 <>
                                                        (FStar_Pervasives_Native.Some
                                                           false))) in
                                          FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "FStar.InteractiveHelpers.Effectful.fst"
                                                     (Prims.of_int (642))
                                                     (Prims.of_int (12))
                                                     (Prims.of_int (642))
                                                     (Prims.of_int (64)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "FStar.InteractiveHelpers.Effectful.fst"
                                                     (Prims.of_int (642))
                                                     (Prims.of_int (9))
                                                     (Prims.of_int (645))
                                                     (Prims.of_int (39)))))
                                            (Obj.magic uu___5)
                                            (fun uu___6 ->
                                               (fun uu___6 ->
                                                  if uu___6
                                                  then
                                                    Obj.magic
                                                      (Obj.repr
                                                         (FStar_Tactics_Effect.lift_div_tac
                                                            (fun uu___7 ->
                                                               (ge,
                                                                 FStar_Pervasives_Native.None))))
                                                  else
                                                    Obj.magic
                                                      (Obj.repr
                                                         (let uu___8 =
                                                            FStar_InteractiveHelpers_Base.genv_push_bv
                                                              ge bv ty false
                                                              FStar_Pervasives_Native.None in
                                                          FStar_Tactics_Effect.tac_bind
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (644))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (644))
                                                                    (Prims.of_int (48)))))
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (645))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (645))
                                                                    (Prims.of_int (39)))))
                                                            (Obj.magic uu___8)
                                                            (fun uu___9 ->
                                                               (fun ge1 ->
                                                                  Obj.magic
                                                                    (
                                                                    find_mem_in_children
                                                                    dbg ge1
                                                                    body))
                                                                 uu___9))))
                                                 uu___6)))) uu___3)))
                | uu___2 ->
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___3 -> (ge, FStar_Pervasives_Native.None)))))
               uu___1)
let (pre_post_to_propositions :
  Prims.bool ->
    FStar_InteractiveHelpers_Base.genv ->
      FStar_InteractiveHelpers_ExploreTerm.effect_type ->
        FStarC_Reflection_Types.term ->
          FStarC_Reflection_Types.binder FStar_Pervasives_Native.option ->
            FStar_InteractiveHelpers_ExploreTerm.type_info ->
              FStarC_Reflection_Types.term FStar_Pervasives_Native.option ->
                FStarC_Reflection_Types.term FStar_Pervasives_Native.option
                  ->
                  FStarC_Reflection_V1_Data.term_view Prims.list ->
                    FStarC_Reflection_V1_Data.term_view Prims.list ->
                      ((FStar_InteractiveHelpers_Base.genv *
                         FStar_InteractiveHelpers_Propositions.proposition
                         FStar_Pervasives_Native.option *
                         FStar_InteractiveHelpers_Propositions.proposition
                         FStar_Pervasives_Native.option),
                        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun dbg ->
    fun ge0 ->
      fun etype ->
        fun v ->
          fun ret_abs_binder ->
            fun ret_type ->
              fun opt_pre ->
                fun opt_post ->
                  fun parents ->
                    fun children ->
                      let uu___ =
                        FStar_InteractiveHelpers_Base.print_dbg dbg
                          "[> pre_post_to_propositions: begin" in
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.InteractiveHelpers.Effectful.fst"
                                 (Prims.of_int (664)) (Prims.of_int (2))
                                 (Prims.of_int (664)) (Prims.of_int (52)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.InteractiveHelpers.Effectful.fst"
                                 (Prims.of_int (665)) (Prims.of_int (2))
                                 (Prims.of_int (742)) (Prims.of_int (26)))))
                        (Obj.magic uu___)
                        (fun uu___1 ->
                           (fun uu___1 ->
                              let uu___2 =
                                let uu___3 =
                                  let uu___4 =
                                    FStar_InteractiveHelpers_Base.option_to_string
                                      FStarC_Tactics_V1_Builtins.term_to_string
                                      opt_pre in
                                  FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.InteractiveHelpers.Effectful.fst"
                                             (Prims.of_int (665))
                                             (Prims.of_int (44))
                                             (Prims.of_int (665))
                                             (Prims.of_int (83)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range "Prims.fst"
                                             (Prims.of_int (611))
                                             (Prims.of_int (19))
                                             (Prims.of_int (611))
                                             (Prims.of_int (31)))))
                                    (Obj.magic uu___4)
                                    (fun uu___5 ->
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___6 ->
                                            Prims.strcat
                                              "- uninstantiated pre: " uu___5)) in
                                FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "FStar.InteractiveHelpers.Effectful.fst"
                                           (Prims.of_int (665))
                                           (Prims.of_int (16))
                                           (Prims.of_int (665))
                                           (Prims.of_int (84)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "FStar.InteractiveHelpers.Effectful.fst"
                                           (Prims.of_int (665))
                                           (Prims.of_int (2))
                                           (Prims.of_int (665))
                                           (Prims.of_int (84)))))
                                  (Obj.magic uu___3)
                                  (fun uu___4 ->
                                     (fun uu___4 ->
                                        Obj.magic
                                          (FStar_InteractiveHelpers_Base.print_dbg
                                             dbg uu___4)) uu___4) in
                              Obj.magic
                                (FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "FStar.InteractiveHelpers.Effectful.fst"
                                            (Prims.of_int (665))
                                            (Prims.of_int (2))
                                            (Prims.of_int (665))
                                            (Prims.of_int (84)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "FStar.InteractiveHelpers.Effectful.fst"
                                            (Prims.of_int (666))
                                            (Prims.of_int (2))
                                            (Prims.of_int (742))
                                            (Prims.of_int (26)))))
                                   (Obj.magic uu___2)
                                   (fun uu___3 ->
                                      (fun uu___3 ->
                                         let uu___4 =
                                           let uu___5 =
                                             let uu___6 =
                                               FStar_InteractiveHelpers_Base.option_to_string
                                                 FStarC_Tactics_V1_Builtins.term_to_string
                                                 opt_post in
                                             FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "FStar.InteractiveHelpers.Effectful.fst"
                                                        (Prims.of_int (666))
                                                        (Prims.of_int (45))
                                                        (Prims.of_int (666))
                                                        (Prims.of_int (85)))))
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Prims.fst"
                                                        (Prims.of_int (611))
                                                        (Prims.of_int (19))
                                                        (Prims.of_int (611))
                                                        (Prims.of_int (31)))))
                                               (Obj.magic uu___6)
                                               (fun uu___7 ->
                                                  FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___8 ->
                                                       Prims.strcat
                                                         "- uninstantiated post: "
                                                         uu___7)) in
                                           FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "FStar.InteractiveHelpers.Effectful.fst"
                                                      (Prims.of_int (666))
                                                      (Prims.of_int (16))
                                                      (Prims.of_int (666))
                                                      (Prims.of_int (86)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "FStar.InteractiveHelpers.Effectful.fst"
                                                      (Prims.of_int (666))
                                                      (Prims.of_int (2))
                                                      (Prims.of_int (666))
                                                      (Prims.of_int (86)))))
                                             (Obj.magic uu___5)
                                             (fun uu___6 ->
                                                (fun uu___6 ->
                                                   Obj.magic
                                                     (FStar_InteractiveHelpers_Base.print_dbg
                                                        dbg uu___6)) uu___6) in
                                         Obj.magic
                                           (FStar_Tactics_Effect.tac_bind
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "FStar.InteractiveHelpers.Effectful.fst"
                                                       (Prims.of_int (666))
                                                       (Prims.of_int (2))
                                                       (Prims.of_int (666))
                                                       (Prims.of_int (86)))))
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "FStar.InteractiveHelpers.Effectful.fst"
                                                       (Prims.of_int (666))
                                                       (Prims.of_int (87))
                                                       (Prims.of_int (742))
                                                       (Prims.of_int (26)))))
                                              (Obj.magic uu___4)
                                              (fun uu___5 ->
                                                 (fun uu___5 ->
                                                    let uu___6 =
                                                      Obj.magic
                                                        (FStar_Tactics_Effect.lift_div_tac
                                                           (fun uu___7 ->
                                                              match ret_abs_binder
                                                              with
                                                              | FStar_Pervasives_Native.None
                                                                  -> []
                                                              | FStar_Pervasives_Native.Some
                                                                  b -> 
                                                                  [b])) in
                                                    Obj.magic
                                                      (FStar_Tactics_Effect.tac_bind
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "FStar.InteractiveHelpers.Effectful.fst"
                                                                  (Prims.of_int (667))
                                                                  (Prims.of_int (12))
                                                                  (Prims.of_int (667))
                                                                  (Prims.of_int (66)))))
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "FStar.InteractiveHelpers.Effectful.fst"
                                                                  (Prims.of_int (667))
                                                                  (Prims.of_int (69))
                                                                  (Prims.of_int (742))
                                                                  (Prims.of_int (26)))))
                                                         (Obj.magic uu___6)
                                                         (fun uu___7 ->
                                                            (fun brs ->
                                                               let uu___7 =
                                                                 match etype
                                                                 with
                                                                 | FStar_InteractiveHelpers_ExploreTerm.E_Lemma
                                                                    ->
                                                                    let uu___8
                                                                    =
                                                                    FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    "E_Lemma" in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (672))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (672))
                                                                    (Prims.of_int (29)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (673))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (673))
                                                                    (Prims.of_int (34)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (ge0,
                                                                    ([], []),
                                                                    ([
                                                                    FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_Const
                                                                    FStarC_Reflection_V2_Data.C_Unit)],
                                                                    []))))
                                                                 | FStar_InteractiveHelpers_ExploreTerm.E_Total
                                                                    ->
                                                                    let uu___8
                                                                    =
                                                                    FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    "E_Total/E_GTotal" in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (675))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (675))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (676))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (676))
                                                                    (Prims.of_int (29)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (ge0,
                                                                    ([], []),
                                                                    ([], []))))
                                                                 | FStar_InteractiveHelpers_ExploreTerm.E_GTotal
                                                                    ->
                                                                    let uu___8
                                                                    =
                                                                    FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    "E_Total/E_GTotal" in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (675))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (675))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (676))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (676))
                                                                    (Prims.of_int (29)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (ge0,
                                                                    ([], []),
                                                                    ([], []))))
                                                                 | FStar_InteractiveHelpers_ExploreTerm.E_PURE
                                                                    ->
                                                                    let uu___8
                                                                    =
                                                                    FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    "E_PURE/E_Pure" in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (678))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (678))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (679))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (679))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (ge0,
                                                                    ([], []),
                                                                    ([v],
                                                                    brs))))
                                                                 | FStar_InteractiveHelpers_ExploreTerm.E_Pure
                                                                    ->
                                                                    let uu___8
                                                                    =
                                                                    FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    "E_PURE/E_Pure" in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (678))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (678))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (679))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (679))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (ge0,
                                                                    ([], []),
                                                                    ([v],
                                                                    brs))))
                                                                 | FStar_InteractiveHelpers_ExploreTerm.E_Stack
                                                                    ->
                                                                    let uu___8
                                                                    =
                                                                    FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    "E_Stack/E_ST" in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (681))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (681))
                                                                    (Prims.of_int (34)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (683))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (695))
                                                                    (Prims.of_int (76)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    let uu___10
                                                                    =
                                                                    FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    "Looking for the initial state in the context" in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (683))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (683))
                                                                    (Prims.of_int (66)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (683))
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (695))
                                                                    (Prims.of_int (76)))))
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
                                                                    find_mem_in_related
                                                                    dbg ge0
                                                                    parents in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (684))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (684))
                                                                    (Prims.of_int (54)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (685))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (695))
                                                                    (Prims.of_int (76)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (fun
                                                                    b1_opt ->
                                                                    let uu___13
                                                                    =
                                                                    FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    "Looking for the final state in the context" in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (685))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (685))
                                                                    (Prims.of_int (64)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (685))
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (695))
                                                                    (Prims.of_int (76)))))
                                                                    (Obj.magic
                                                                    uu___13)
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    let uu___15
                                                                    =
                                                                    find_mem_in_related
                                                                    dbg ge0
                                                                    children in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (686))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (686))
                                                                    (Prims.of_int (55)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (686))
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (695))
                                                                    (Prims.of_int (76)))))
                                                                    (Obj.magic
                                                                    uu___15)
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    (fun
                                                                    b2_opt ->
                                                                    let uu___16
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    fun
                                                                    opt_bvt
                                                                    ->
                                                                    fun
                                                                    basename
                                                                    ->
                                                                    fun ge ->
                                                                    match opt_bvt
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (bv, ty)
                                                                    ->
                                                                    let uu___18
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.pack
                                                                    (FStarC_Reflection_V1_Data.Tv_Var
                                                                    bv) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (690))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (690))
                                                                    (Prims.of_int (43)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (690))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (690))
                                                                    (Prims.of_int (64)))))
                                                                    (Obj.magic
                                                                    uu___18)
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    (uu___19,
                                                                    (FStar_Reflection_V1_Derived.mk_binder
                                                                    bv ty),
                                                                    ge)))
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_InteractiveHelpers_Base.genv_push_fresh_var
                                                                    ge
                                                                    basename
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Monotonic";
                                                                    "HyperStack";
                                                                    "mem"]))))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (689))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (691))
                                                                    (Prims.of_int (59)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (692))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (695))
                                                                    (Prims.of_int (76)))))
                                                                    (Obj.magic
                                                                    uu___16)
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    (fun
                                                                    opt_push_fresh_state
                                                                    ->
                                                                    let uu___17
                                                                    =
                                                                    opt_push_fresh_state
                                                                    b1_opt
                                                                    "__h0_"
                                                                    ge0 in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (693))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (693))
                                                                    (Prims.of_int (63)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (692))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (695))
                                                                    (Prims.of_int (76)))))
                                                                    (Obj.magic
                                                                    uu___17)
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    match uu___18
                                                                    with
                                                                    | 
                                                                    (h1, b1,
                                                                    ge1) ->
                                                                    let uu___19
                                                                    =
                                                                    opt_push_fresh_state
                                                                    b2_opt
                                                                    "__h1_"
                                                                    ge1 in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (694))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (694))
                                                                    (Prims.of_int (63)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (693))
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (695))
                                                                    (Prims.of_int (76)))))
                                                                    (Obj.magic
                                                                    uu___19)
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___21
                                                                    ->
                                                                    match uu___20
                                                                    with
                                                                    | 
                                                                    (h2, b2,
                                                                    ge2) ->
                                                                    (ge2,
                                                                    ([h1],
                                                                    [b1]),
                                                                    ([h1;
                                                                    v;
                                                                    h2],
                                                                    (FStar_List_Tot_Base.flatten
                                                                    [
                                                                    [b1];
                                                                    brs;
                                                                    [b2]])))))))
                                                                    uu___18)))
                                                                    uu___17)))
                                                                    uu___16)))
                                                                    uu___14)))
                                                                    uu___13)))
                                                                    uu___11)))
                                                                    uu___9)
                                                                 | FStar_InteractiveHelpers_ExploreTerm.E_ST
                                                                    ->
                                                                    let uu___8
                                                                    =
                                                                    FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    "E_Stack/E_ST" in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (681))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (681))
                                                                    (Prims.of_int (34)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (683))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (695))
                                                                    (Prims.of_int (76)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    let uu___10
                                                                    =
                                                                    FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    "Looking for the initial state in the context" in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (683))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (683))
                                                                    (Prims.of_int (66)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (683))
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (695))
                                                                    (Prims.of_int (76)))))
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
                                                                    find_mem_in_related
                                                                    dbg ge0
                                                                    parents in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (684))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (684))
                                                                    (Prims.of_int (54)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (685))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (695))
                                                                    (Prims.of_int (76)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (fun
                                                                    b1_opt ->
                                                                    let uu___13
                                                                    =
                                                                    FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    "Looking for the final state in the context" in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (685))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (685))
                                                                    (Prims.of_int (64)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (685))
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (695))
                                                                    (Prims.of_int (76)))))
                                                                    (Obj.magic
                                                                    uu___13)
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    let uu___15
                                                                    =
                                                                    find_mem_in_related
                                                                    dbg ge0
                                                                    children in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (686))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (686))
                                                                    (Prims.of_int (55)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (686))
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (695))
                                                                    (Prims.of_int (76)))))
                                                                    (Obj.magic
                                                                    uu___15)
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    (fun
                                                                    b2_opt ->
                                                                    let uu___16
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    fun
                                                                    opt_bvt
                                                                    ->
                                                                    fun
                                                                    basename
                                                                    ->
                                                                    fun ge ->
                                                                    match opt_bvt
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (bv, ty)
                                                                    ->
                                                                    let uu___18
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.pack
                                                                    (FStarC_Reflection_V1_Data.Tv_Var
                                                                    bv) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (690))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (690))
                                                                    (Prims.of_int (43)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (690))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (690))
                                                                    (Prims.of_int (64)))))
                                                                    (Obj.magic
                                                                    uu___18)
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    (uu___19,
                                                                    (FStar_Reflection_V1_Derived.mk_binder
                                                                    bv ty),
                                                                    ge)))
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_InteractiveHelpers_Base.genv_push_fresh_var
                                                                    ge
                                                                    basename
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Monotonic";
                                                                    "HyperStack";
                                                                    "mem"]))))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (689))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (691))
                                                                    (Prims.of_int (59)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (692))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (695))
                                                                    (Prims.of_int (76)))))
                                                                    (Obj.magic
                                                                    uu___16)
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    (fun
                                                                    opt_push_fresh_state
                                                                    ->
                                                                    let uu___17
                                                                    =
                                                                    opt_push_fresh_state
                                                                    b1_opt
                                                                    "__h0_"
                                                                    ge0 in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (693))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (693))
                                                                    (Prims.of_int (63)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (692))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (695))
                                                                    (Prims.of_int (76)))))
                                                                    (Obj.magic
                                                                    uu___17)
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    match uu___18
                                                                    with
                                                                    | 
                                                                    (h1, b1,
                                                                    ge1) ->
                                                                    let uu___19
                                                                    =
                                                                    opt_push_fresh_state
                                                                    b2_opt
                                                                    "__h1_"
                                                                    ge1 in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (694))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (694))
                                                                    (Prims.of_int (63)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (693))
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (695))
                                                                    (Prims.of_int (76)))))
                                                                    (Obj.magic
                                                                    uu___19)
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___21
                                                                    ->
                                                                    match uu___20
                                                                    with
                                                                    | 
                                                                    (h2, b2,
                                                                    ge2) ->
                                                                    (ge2,
                                                                    ([h1],
                                                                    [b1]),
                                                                    ([h1;
                                                                    v;
                                                                    h2],
                                                                    (FStar_List_Tot_Base.flatten
                                                                    [
                                                                    [b1];
                                                                    brs;
                                                                    [b2]])))))))
                                                                    uu___18)))
                                                                    uu___17)))
                                                                    uu___16)))
                                                                    uu___14)))
                                                                    uu___13)))
                                                                    uu___11)))
                                                                    uu___9)
                                                                 | FStar_InteractiveHelpers_ExploreTerm.E_Unknown
                                                                    ->
                                                                    let uu___8
                                                                    =
                                                                    check_opt_pre_post_type
                                                                    dbg
                                                                    ge0.FStar_InteractiveHelpers_Base.env
                                                                    opt_pre
                                                                    ret_type.FStar_InteractiveHelpers_ExploreTerm.ty
                                                                    opt_post in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (703))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (703))
                                                                    (Prims.of_int (84)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (704))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (723))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    pp_type
                                                                    ->
                                                                    match pp_type
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (PP_Pure)
                                                                    ->
                                                                    let uu___9
                                                                    =
                                                                    FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    "PP_Pure" in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (706))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (706))
                                                                    (Prims.of_int (31)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (708))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (708))
                                                                    (Prims.of_int (33)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (ge0,
                                                                    ([], []),
                                                                    ([v],
                                                                    brs)))))
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (PP_State
                                                                    state_type)
                                                                    ->
                                                                    let uu___9
                                                                    =
                                                                    FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    "PP_State" in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (710))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (710))
                                                                    (Prims.of_int (32)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (710))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (713))
                                                                    (Prims.of_int (78)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    let uu___11
                                                                    =
                                                                    FStar_InteractiveHelpers_Base.genv_push_two_fresh_vars
                                                                    ge0 "__s"
                                                                    state_type in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (712))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (712))
                                                                    (Prims.of_int (79)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (710))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (713))
                                                                    (Prims.of_int (78)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    match uu___12
                                                                    with
                                                                    | 
                                                                    (s1, b1,
                                                                    s2, b2,
                                                                    ge1) ->
                                                                    (ge1,
                                                                    ([s1],
                                                                    [b1]),
                                                                    ([s1;
                                                                    v;
                                                                    s2],
                                                                    (FStar_List_Tot_Base.flatten
                                                                    [
                                                                    [b1];
                                                                    brs;
                                                                    [b2]])))))))
                                                                    uu___10))
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (PP_Unknown)
                                                                    ->
                                                                    let uu___9
                                                                    =
                                                                    FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    "PP_Unknown" in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (715))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (715))
                                                                    (Prims.of_int (34)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (715))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (719))
                                                                    (Prims.of_int (67)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    let uu___11
                                                                    =
                                                                    introduce_variables_for_opt_abs
                                                                    ge0
                                                                    opt_pre in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (717))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (717))
                                                                    (Prims.of_int (86)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (715))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (719))
                                                                    (Prims.of_int (67)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    match uu___12
                                                                    with
                                                                    | 
                                                                    (pre_values,
                                                                    pre_binders,
                                                                    ge1) ->
                                                                    let uu___13
                                                                    =
                                                                    introduce_variables_for_opt_abs
                                                                    ge1
                                                                    opt_post in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (718))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (718))
                                                                    (Prims.of_int (89)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (717))
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (719))
                                                                    (Prims.of_int (67)))))
                                                                    (Obj.magic
                                                                    uu___13)
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    match uu___14
                                                                    with
                                                                    | 
                                                                    (post_values,
                                                                    post_binders,
                                                                    ge11) ->
                                                                    (ge11,
                                                                    (pre_values,
                                                                    pre_binders),
                                                                    (post_values,
                                                                    post_binders))))))
                                                                    uu___12)))
                                                                    uu___10))
                                                                    | 
                                                                    uu___9 ->
                                                                    let uu___10
                                                                    =
                                                                    FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    "No pre and no post" in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (721))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (721))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (723))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (723))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (ge0,
                                                                    ([], []),
                                                                    ([], []))))))
                                                                    uu___9) in
                                                               Obj.magic
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (670))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (724))
                                                                    (Prims.of_int (9)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (667))
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (742))
                                                                    (Prims.of_int (26)))))
                                                                    (
                                                                    Obj.magic
                                                                    uu___7)
                                                                    (
                                                                    fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    match uu___8
                                                                    with
                                                                    | 
                                                                    (ge3,
                                                                    (pre_values,
                                                                    pre_binders),
                                                                    (post_values,
                                                                    post_binders))
                                                                    ->
                                                                    let uu___9
                                                                    =
                                                                    FStar_InteractiveHelpers_Base.opt_mk_app_norm
                                                                    ge3.FStar_InteractiveHelpers_Base.env
                                                                    opt_pre
                                                                    pre_values in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (728))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (728))
                                                                    (Prims.of_int (59)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (728))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (742))
                                                                    (Prims.of_int (26)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    pre_prop
                                                                    ->
                                                                    let uu___10
                                                                    =
                                                                    FStar_Tactics_V1_Derived.try_with
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    FStar_InteractiveHelpers_Base.opt_mk_app_norm
                                                                    ge3.FStar_InteractiveHelpers_Base.env
                                                                    opt_post
                                                                    post_values)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    let uu___12
                                                                    =
                                                                    FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    "Dropping a postcondition because of incoherent typing" in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (737))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (737))
                                                                    (Prims.of_int (75)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (738))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (738))
                                                                    (Prims.of_int (10)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    FStar_Pervasives_Native.None))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (734))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (738))
                                                                    (Prims.of_int (10)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (741))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (742))
                                                                    (Prims.of_int (26)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    post_prop
                                                                    ->
                                                                    let uu___11
                                                                    =
                                                                    FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    "[> pre_post_to_propositions: end" in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (741))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (741))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (742))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (742))
                                                                    (Prims.of_int (26)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (ge3,
                                                                    pre_prop,
                                                                    post_prop)))))
                                                                    uu___11)))
                                                                    uu___10)))
                                                                    uu___8)))
                                                              uu___7)))
                                                   uu___5))) uu___3))) uu___1)
let (eterm_info_to_assertions :
  Prims.bool ->
    Prims.bool ->
      Prims.bool ->
        FStar_InteractiveHelpers_Base.genv ->
          FStarC_Reflection_Types.term ->
            Prims.bool ->
              Prims.bool ->
                eterm_info ->
                  FStarC_Reflection_Types.term FStar_Pervasives_Native.option
                    ->
                    FStar_InteractiveHelpers_ExploreTerm.typ_or_comp
                      FStar_Pervasives_Native.option ->
                      FStarC_Reflection_V1_Data.term_view Prims.list ->
                        FStarC_Reflection_V1_Data.term_view Prims.list ->
                          ((FStar_InteractiveHelpers_Base.genv *
                             FStar_InteractiveHelpers_Propositions.assertions),
                            unit) FStar_Tactics_Effect.tac_repr)
  =
  fun dbg ->
    fun with_gpre ->
      fun with_gpost ->
        fun ge ->
          fun t ->
            fun is_let ->
              fun is_assert ->
                fun info ->
                  fun bind_var ->
                    fun opt_c ->
                      fun parents ->
                        fun children ->
                          let uu___ =
                            FStar_InteractiveHelpers_Base.print_dbg dbg
                              "[> eterm_info_to_assertions" in
                          FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.InteractiveHelpers.Effectful.fst"
                                     (Prims.of_int (766)) (Prims.of_int (2))
                                     (Prims.of_int (766)) (Prims.of_int (45)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.InteractiveHelpers.Effectful.fst"
                                     (Prims.of_int (766)) (Prims.of_int (46))
                                     (Prims.of_int (962)) (Prims.of_int (7)))))
                            (Obj.magic uu___)
                            (fun uu___1 ->
                               (fun uu___1 ->
                                  let uu___2 =
                                    Obj.magic
                                      (FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___3 -> info.einfo)) in
                                  Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.InteractiveHelpers.Effectful.fst"
                                                (Prims.of_int (771))
                                                (Prims.of_int (14))
                                                (Prims.of_int (771))
                                                (Prims.of_int (24)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.InteractiveHelpers.Effectful.fst"
                                                (Prims.of_int (771))
                                                (Prims.of_int (27))
                                                (Prims.of_int (962))
                                                (Prims.of_int (7)))))
                                       (Obj.magic uu___2)
                                       (fun uu___3 ->
                                          (fun einfo ->
                                             let uu___3 =
                                               match bind_var with
                                               | FStar_Pervasives_Native.Some
                                                   v ->
                                                   Obj.magic
                                                     (Obj.repr
                                                        (FStar_Tactics_Effect.lift_div_tac
                                                           (fun uu___4 ->
                                                              (ge, v,
                                                                FStar_Pervasives_Native.None))))
                                               | FStar_Pervasives_Native.None
                                                   ->
                                                   Obj.magic
                                                     (Obj.repr
                                                        (if
                                                           effect_type_is_stateful
                                                             einfo.ei_type
                                                         then
                                                           Obj.repr
                                                             (let uu___4 =
                                                                FStar_InteractiveHelpers_ExploreTerm.is_unit_type
                                                                  (einfo.ei_ret_type).FStar_InteractiveHelpers_ExploreTerm.ty in
                                                              FStar_Tactics_Effect.tac_bind
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (782))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (782))
                                                                    (Prims.of_int (44)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (782))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (788))
                                                                    (Prims.of_int (53)))))
                                                                (Obj.magic
                                                                   uu___4)
                                                                (fun uu___5
                                                                   ->
                                                                   (fun
                                                                    uu___5 ->
                                                                    if uu___5
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    (ge,
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_Const
                                                                    FStarC_Reflection_V2_Data.C_Unit)),
                                                                    FStar_Pervasives_Native.None))))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___7
                                                                    =
                                                                    FStar_InteractiveHelpers_Base.fresh_binder
                                                                    ge.FStar_InteractiveHelpers_Base.env
                                                                    "__ret"
                                                                    (einfo.ei_ret_type).FStar_InteractiveHelpers_ExploreTerm.ty in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (785))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (785))
                                                                    (Prims.of_int (66)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (785))
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (788))
                                                                    (Prims.of_int (53)))))
                                                                    (Obj.magic
                                                                    uu___7)
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun b ->
                                                                    let uu___8
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Reflection_V1_Derived.bv_of_binder
                                                                    b)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (786))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (786))
                                                                    (Prims.of_int (33)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (786))
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (788))
                                                                    (Prims.of_int (53)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun bv
                                                                    ->
                                                                    let uu___9
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.pack
                                                                    (FStarC_Reflection_V1_Data.Tv_Var
                                                                    bv) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (787))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (787))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (788))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (788))
                                                                    (Prims.of_int (53)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun tm
                                                                    ->
                                                                    let uu___10
                                                                    =
                                                                    FStar_InteractiveHelpers_Base.genv_push_binder
                                                                    ge b true
                                                                    FStar_Pervasives_Native.None in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (788))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (788))
                                                                    (Prims.of_int (41)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (788))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (788))
                                                                    (Prims.of_int (53)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (uu___11,
                                                                    tm,
                                                                    (FStar_Pervasives_Native.Some
                                                                    b))))))
                                                                    uu___10)))
                                                                    uu___9)))
                                                                    uu___8))))
                                                                    uu___5))
                                                         else
                                                           Obj.repr
                                                             (FStar_Tactics_Effect.lift_div_tac
                                                                (fun uu___5
                                                                   ->
                                                                   (ge, t,
                                                                    FStar_Pervasives_Native.None))))) in
                                             Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.InteractiveHelpers.Effectful.fst"
                                                           (Prims.of_int (773))
                                                           (Prims.of_int (4))
                                                           (Prims.of_int (789))
                                                           (Prims.of_int (22)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.InteractiveHelpers.Effectful.fst"
                                                           (Prims.of_int (771))
                                                           (Prims.of_int (27))
                                                           (Prims.of_int (962))
                                                           (Prims.of_int (7)))))
                                                  (Obj.magic uu___3)
                                                  (fun uu___4 ->
                                                     (fun uu___4 ->
                                                        match uu___4 with
                                                        | (ge0, v, opt_b) ->
                                                            let uu___5 =
                                                              Obj.magic
                                                                (FStar_Tactics_Effect.lift_div_tac
                                                                   (fun
                                                                    uu___6 ->
                                                                    v)) in
                                                            Obj.magic
                                                              (FStar_Tactics_Effect.tac_bind
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (792))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (962))
                                                                    (Prims.of_int (7)))))
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (792))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (962))
                                                                    (Prims.of_int (7)))))
                                                                 (Obj.magic
                                                                    uu___5)
                                                                 (fun uu___6
                                                                    ->
                                                                    (fun v1
                                                                    ->
                                                                    let uu___6
                                                                    =
                                                                    FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    "> Instantiating local pre/post" in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (792))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (792))
                                                                    (Prims.of_int (53)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (792))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (962))
                                                                    (Prims.of_int (7)))))
                                                                    (Obj.magic
                                                                    uu___6)
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    let uu___8
                                                                    =
                                                                    pre_post_to_propositions
                                                                    dbg ge0
                                                                    einfo.ei_type
                                                                    v1 opt_b
                                                                    einfo.ei_ret_type
                                                                    einfo.ei_pre
                                                                    einfo.ei_post
                                                                    parents
                                                                    children in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (794))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (795))
                                                                    (Prims.of_int (72)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (792))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (962))
                                                                    (Prims.of_int (7)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    match uu___9
                                                                    with
                                                                    | 
                                                                    (ge1,
                                                                    pre_prop,
                                                                    post_prop)
                                                                    ->
                                                                    let uu___10
                                                                    =
                                                                    let uu___11
                                                                    =
                                                                    let uu___12
                                                                    =
                                                                    FStar_InteractiveHelpers_Base.option_to_string
                                                                    FStarC_Tactics_V1_Builtins.term_to_string
                                                                    pre_prop in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (796))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (796))
                                                                    (Prims.of_int (74)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    Prims.strcat
                                                                    "- pre prop: "
                                                                    uu___13)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (796))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (796))
                                                                    (Prims.of_int (75)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (796))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (796))
                                                                    (Prims.of_int (75)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    uu___12))
                                                                    uu___12) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (796))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (796))
                                                                    (Prims.of_int (75)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (797))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (962))
                                                                    (Prims.of_int (7)))))
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
                                                                    let uu___14
                                                                    =
                                                                    FStar_InteractiveHelpers_Base.option_to_string
                                                                    FStarC_Tactics_V1_Builtins.term_to_string
                                                                    post_prop in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (797))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (797))
                                                                    (Prims.of_int (76)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___14)
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    Prims.strcat
                                                                    "- post prop: "
                                                                    uu___15)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (797))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (797))
                                                                    (Prims.of_int (77)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (797))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (797))
                                                                    (Prims.of_int (77)))))
                                                                    (Obj.magic
                                                                    uu___13)
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    uu___14))
                                                                    uu___14) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (797))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (797))
                                                                    (Prims.of_int (77)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (801))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (962))
                                                                    (Prims.of_int (7)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    if
                                                                    is_assert
                                                                    then
                                                                    let uu___14
                                                                    =
                                                                    FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    "The term is an assert: only keep the postcondition" in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (803))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (803))
                                                                    (Prims.of_int (70)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (804))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (804))
                                                                    (Prims.of_int (53)))))
                                                                    (Obj.magic
                                                                    uu___14)
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    (ge1,
                                                                    {
                                                                    FStar_InteractiveHelpers_Propositions.pres
                                                                    =
                                                                    (FStar_InteractiveHelpers_Base.opt_cons
                                                                    post_prop
                                                                    []);
                                                                    FStar_InteractiveHelpers_Propositions.posts
                                                                    = []
                                                                    }))))
                                                                    else
                                                                    (let uu___15
                                                                    =
                                                                    let uu___16
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    with_gpre
                                                                    ||
                                                                    ((Prims.op_Negation
                                                                    is_let)
                                                                    &&
                                                                    with_gpost))) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (812))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (812))
                                                                    (Prims.of_int (70)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (813))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (934))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___16)
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    (fun
                                                                    with_goal
                                                                    ->
                                                                    match 
                                                                    (opt_c,
                                                                    with_goal)
                                                                    with
                                                                    | 
                                                                    (FStar_Pervasives_Native.Some
                                                                    c, true)
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___17
                                                                    =
                                                                    typ_or_comp_to_effect_info
                                                                    dbg ge1 c in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (815))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (815))
                                                                    (Prims.of_int (53)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (816))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (932))
                                                                    (Prims.of_int (62)))))
                                                                    (Obj.magic
                                                                    uu___17)
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    (fun ei
                                                                    ->
                                                                    let uu___18
                                                                    =
                                                                    let uu___19
                                                                    =
                                                                    let uu___20
                                                                    =
                                                                    effect_info_to_string
                                                                    ei in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (816))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (816))
                                                                    (Prims.of_int (69)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
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
                                                                    "- target effect: "
                                                                    uu___21)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (816))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (816))
                                                                    (Prims.of_int (70)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (816))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (816))
                                                                    (Prims.of_int (70)))))
                                                                    (Obj.magic
                                                                    uu___19)
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    uu___20))
                                                                    uu___20) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (816))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (816))
                                                                    (Prims.of_int (70)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (817))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (932))
                                                                    (Prims.of_int (62)))))
                                                                    (Obj.magic
                                                                    uu___18)
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    let uu___20
                                                                    =
                                                                    let uu___21
                                                                    =
                                                                    let uu___22
                                                                    =
                                                                    FStar_InteractiveHelpers_Base.option_to_string
                                                                    FStarC_Tactics_V1_Builtins.term_to_string
                                                                    ei.ei_pre in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (817))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (817))
                                                                    (Prims.of_int (91)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
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
                                                                    "- global unfilt. pre: "
                                                                    uu___23)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (817))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (817))
                                                                    (Prims.of_int (92)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (817))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (817))
                                                                    (Prims.of_int (92)))))
                                                                    (Obj.magic
                                                                    uu___21)
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    uu___22))
                                                                    uu___22) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (817))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (817))
                                                                    (Prims.of_int (92)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (818))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (932))
                                                                    (Prims.of_int (62)))))
                                                                    (Obj.magic
                                                                    uu___20)
                                                                    (fun
                                                                    uu___21
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
                                                                    FStar_InteractiveHelpers_Base.option_to_string
                                                                    FStarC_Tactics_V1_Builtins.term_to_string
                                                                    ei.ei_post in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (818))
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (818))
                                                                    (Prims.of_int (93)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
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
                                                                    "- global unfilt. post: "
                                                                    uu___25)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (818))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (818))
                                                                    (Prims.of_int (94)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (818))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (818))
                                                                    (Prims.of_int (94)))))
                                                                    (Obj.magic
                                                                    uu___23)
                                                                    (fun
                                                                    uu___24
                                                                    ->
                                                                    (fun
                                                                    uu___24
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    uu___24))
                                                                    uu___24) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (818))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (818))
                                                                    (Prims.of_int (94)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (818))
                                                                    (Prims.of_int (95))
                                                                    (Prims.of_int (932))
                                                                    (Prims.of_int (62)))))
                                                                    (Obj.magic
                                                                    uu___22)
                                                                    (fun
                                                                    uu___23
                                                                    ->
                                                                    (fun
                                                                    uu___23
                                                                    ->
                                                                    let uu___24
                                                                    =
                                                                    if
                                                                    with_gpre
                                                                    then
                                                                    let uu___25
                                                                    =
                                                                    FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    "Generating assertions from the global parameters' types" in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (825))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (825))
                                                                    (Prims.of_int (83)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (826))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (857))
                                                                    (Prims.of_int (34)))))
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
                                                                    FStar_InteractiveHelpers_Base.genv_to_string
                                                                    ge1 in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (826))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (826))
                                                                    (Prims.of_int (65)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___29)
                                                                    (fun
                                                                    uu___30
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___31
                                                                    ->
                                                                    Prims.strcat
                                                                    "Current genv:\n"
                                                                    uu___30)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (826))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (826))
                                                                    (Prims.of_int (66)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (826))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (826))
                                                                    (Prims.of_int (66)))))
                                                                    (Obj.magic
                                                                    uu___28)
                                                                    (fun
                                                                    uu___29
                                                                    ->
                                                                    (fun
                                                                    uu___29
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    uu___29))
                                                                    uu___29) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (826))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (826))
                                                                    (Prims.of_int (66)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (826))
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (857))
                                                                    (Prims.of_int (34)))))
                                                                    (Obj.magic
                                                                    uu___27)
                                                                    (fun
                                                                    uu___28
                                                                    ->
                                                                    (fun
                                                                    uu___28
                                                                    ->
                                                                    let uu___29
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___30
                                                                    ->
                                                                    FStar_List_Tot_Base.rev
                                                                    (FStar_List_Tot_Base.map
                                                                    (fun x ->
                                                                    (x,
                                                                    (FStar_Reflection_V1_Derived.type_of_binder
                                                                    x)))
                                                                    (FStar_InteractiveHelpers_ExploreTerm.params_of_typ_or_comp
                                                                    c)))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (831))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (831))
                                                                    (Prims.of_int (91)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (832))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (857))
                                                                    (Prims.of_int (34)))))
                                                                    (Obj.magic
                                                                    uu___29)
                                                                    (fun
                                                                    uu___30
                                                                    ->
                                                                    (fun
                                                                    params ->
                                                                    let uu___30
                                                                    =
                                                                    FStar_Tactics_Util.iteri
                                                                    (fun i ->
                                                                    fun
                                                                    uu___31
                                                                    ->
                                                                    match uu___31
                                                                    with
                                                                    | 
                                                                    (b,
                                                                    uu___32)
                                                                    ->
                                                                    let uu___33
                                                                    =
                                                                    let uu___34
                                                                    =
                                                                    let uu___35
                                                                    =
                                                                    let uu___36
                                                                    =
                                                                    FStar_Tactics_V1_Derived.binder_to_string
                                                                    b in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (833))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (833))
                                                                    (Prims.of_int (65)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___36)
                                                                    (fun
                                                                    uu___37
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___38
                                                                    ->
                                                                    Prims.strcat
                                                                    ": "
                                                                    uu___37)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (833))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (833))
                                                                    (Prims.of_int (65)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___35)
                                                                    (fun
                                                                    uu___36
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___37
                                                                    ->
                                                                    Prims.strcat
                                                                    (Prims.string_of_int
                                                                    i)
                                                                    uu___36)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (832))
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (833))
                                                                    (Prims.of_int (65)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___34)
                                                                    (fun
                                                                    uu___35
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___36
                                                                    ->
                                                                    Prims.strcat
                                                                    "Global parameter "
                                                                    uu___35)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (832))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (833))
                                                                    (Prims.of_int (66)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (832))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (833))
                                                                    (Prims.of_int (66)))))
                                                                    (Obj.magic
                                                                    uu___33)
                                                                    (fun
                                                                    uu___34
                                                                    ->
                                                                    (fun
                                                                    uu___34
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    uu___34))
                                                                    uu___34))
                                                                    params in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (832))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (833))
                                                                    (Prims.of_int (74)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (833))
                                                                    (Prims.of_int (75))
                                                                    (Prims.of_int (857))
                                                                    (Prims.of_int (34)))))
                                                                    (Obj.magic
                                                                    uu___30)
                                                                    (fun
                                                                    uu___31
                                                                    ->
                                                                    (fun
                                                                    uu___31
                                                                    ->
                                                                    let uu___32
                                                                    =
                                                                    FStar_Tactics_Util.filter
                                                                    (fun
                                                                    uu___33
                                                                    ->
                                                                    (fun
                                                                    uu___33
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___34
                                                                    ->
                                                                    match uu___33
                                                                    with
                                                                    | 
                                                                    (b,
                                                                    uu___35)
                                                                    ->
                                                                    Prims.op_Negation
                                                                    (FStar_InteractiveHelpers_Base.binder_is_shadowed
                                                                    ge1 b))))
                                                                    uu___33)
                                                                    params in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (835))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (835))
                                                                    (Prims.of_int (84)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (835))
                                                                    (Prims.of_int (87))
                                                                    (Prims.of_int (857))
                                                                    (Prims.of_int (34)))))
                                                                    (Obj.magic
                                                                    uu___32)
                                                                    (fun
                                                                    uu___33
                                                                    ->
                                                                    (fun
                                                                    params1
                                                                    ->
                                                                    let uu___33
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___34
                                                                    ->
                                                                    fun x ->
                                                                    let uu___35
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___36
                                                                    -> x)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (838))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (838))
                                                                    (Prims.of_int (27)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (837))
                                                                    (Prims.of_int (71))
                                                                    (Prims.of_int (854))
                                                                    (Prims.of_int (22)))))
                                                                    (Obj.magic
                                                                    uu___35)
                                                                    (fun
                                                                    uu___36
                                                                    ->
                                                                    (fun
                                                                    uu___36
                                                                    ->
                                                                    match uu___36
                                                                    with
                                                                    | 
                                                                    (b, ty)
                                                                    ->
                                                                    let uu___37
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___38
                                                                    ->
                                                                    FStar_Reflection_V1_Derived.bv_of_binder
                                                                    b)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (839))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (839))
                                                                    (Prims.of_int (37)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (840))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (854))
                                                                    (Prims.of_int (22)))))
                                                                    (Obj.magic
                                                                    uu___37)
                                                                    (fun
                                                                    uu___38
                                                                    ->
                                                                    (fun bv
                                                                    ->
                                                                    let uu___38
                                                                    =
                                                                    let uu___39
                                                                    =
                                                                    let uu___40
                                                                    =
                                                                    FStar_Tactics_V1_Derived.binder_to_string
                                                                    b in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (840))
                                                                    (Prims.of_int (79))
                                                                    (Prims.of_int (840))
                                                                    (Prims.of_int (97)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___40)
                                                                    (fun
                                                                    uu___41
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___42
                                                                    ->
                                                                    Prims.strcat
                                                                    "Generating assertions from global parameter: "
                                                                    uu___41)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (840))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (840))
                                                                    (Prims.of_int (98)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (840))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (840))
                                                                    (Prims.of_int (98)))))
                                                                    (Obj.magic
                                                                    uu___39)
                                                                    (fun
                                                                    uu___40
                                                                    ->
                                                                    (fun
                                                                    uu___40
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    uu___40))
                                                                    uu___40) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (840))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (840))
                                                                    (Prims.of_int (98)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (840))
                                                                    (Prims.of_int (99))
                                                                    (Prims.of_int (854))
                                                                    (Prims.of_int (22)))))
                                                                    (Obj.magic
                                                                    uu___38)
                                                                    (fun
                                                                    uu___39
                                                                    ->
                                                                    (fun
                                                                    uu___39
                                                                    ->
                                                                    let uu___40
                                                                    =
                                                                    FStar_InteractiveHelpers_ExploreTerm.get_type_info_from_type
                                                                    ty in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (841))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (841))
                                                                    (Prims.of_int (52)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (841))
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (854))
                                                                    (Prims.of_int (22)))))
                                                                    (Obj.magic
                                                                    uu___40)
                                                                    (fun
                                                                    uu___41
                                                                    ->
                                                                    (fun
                                                                    tinfo ->
                                                                    let uu___41
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.pack
                                                                    (FStarC_Reflection_V1_Data.Tv_Var
                                                                    bv) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (842))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (842))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (842))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (854))
                                                                    (Prims.of_int (22)))))
                                                                    (Obj.magic
                                                                    uu___41)
                                                                    (fun
                                                                    uu___42
                                                                    ->
                                                                    (fun v2
                                                                    ->
                                                                    let uu___42
                                                                    =
                                                                    mk_has_type
                                                                    v2
                                                                    tinfo.FStar_InteractiveHelpers_ExploreTerm.ty in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (843))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (843))
                                                                    (Prims.of_int (45)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (843))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (854))
                                                                    (Prims.of_int (22)))))
                                                                    (Obj.magic
                                                                    uu___42)
                                                                    (fun
                                                                    uu___43
                                                                    ->
                                                                    (fun p1
                                                                    ->
                                                                    let uu___43
                                                                    =
                                                                    match 
                                                                    tinfo.FStar_InteractiveHelpers_ExploreTerm.refin
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___44
                                                                    -> [])))
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    r ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___44
                                                                    =
                                                                    FStar_InteractiveHelpers_Base.mk_app_norm
                                                                    ge1.FStar_InteractiveHelpers_Base.env
                                                                    r [v2] in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (847))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (847))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (850))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (852))
                                                                    (Prims.of_int (76)))))
                                                                    (Obj.magic
                                                                    uu___44)
                                                                    (fun
                                                                    uu___45
                                                                    ->
                                                                    (fun p2
                                                                    ->
                                                                    let uu___45
                                                                    =
                                                                    FStar_InteractiveHelpers_ExploreTerm.term_has_shadowed_variables
                                                                    ge1 p2 in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (850))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (850))
                                                                    (Prims.of_int (53)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (850))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (852))
                                                                    (Prims.of_int (76)))))
                                                                    (Obj.magic
                                                                    uu___45)
                                                                    (fun
                                                                    uu___46
                                                                    ->
                                                                    (fun
                                                                    uu___46
                                                                    ->
                                                                    if
                                                                    uu___46
                                                                    then
                                                                    let uu___47
                                                                    =
                                                                    FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    "Discarding type refinement because of shadowed variables" in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (851))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (851))
                                                                    (Prims.of_int (99)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (851))
                                                                    (Prims.of_int (101))
                                                                    (Prims.of_int (851))
                                                                    (Prims.of_int (103)))))
                                                                    (Obj.magic
                                                                    uu___47)
                                                                    (fun
                                                                    uu___48
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___49
                                                                    -> [])))
                                                                    else
                                                                    (let uu___48
                                                                    =
                                                                    FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    "Keeping type refinement" in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (852))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (852))
                                                                    (Prims.of_int (66)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (852))
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (852))
                                                                    (Prims.of_int (72)))))
                                                                    (Obj.magic
                                                                    uu___48)
                                                                    (fun
                                                                    uu___49
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___50
                                                                    -> [p2])))))
                                                                    uu___46)))
                                                                    uu___45))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (844))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (852))
                                                                    (Prims.of_int (76)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (854))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (854))
                                                                    (Prims.of_int (22)))))
                                                                    (Obj.magic
                                                                    uu___43)
                                                                    (fun pl
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___44
                                                                    -> p1 ::
                                                                    pl))))
                                                                    uu___43)))
                                                                    uu___42)))
                                                                    uu___41)))
                                                                    uu___39)))
                                                                    uu___38)))
                                                                    uu___36))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (837))
                                                                    (Prims.of_int (71))
                                                                    (Prims.of_int (854))
                                                                    (Prims.of_int (22)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (855))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (857))
                                                                    (Prims.of_int (34)))))
                                                                    (Obj.magic
                                                                    uu___33)
                                                                    (fun
                                                                    uu___34
                                                                    ->
                                                                    (fun
                                                                    param_to_props
                                                                    ->
                                                                    let uu___34
                                                                    =
                                                                    FStar_Tactics_Util.map
                                                                    param_to_props
                                                                    params1 in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (856))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (856))
                                                                    (Prims.of_int (49)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (857))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (857))
                                                                    (Prims.of_int (34)))))
                                                                    (Obj.magic
                                                                    uu___34)
                                                                    (fun
                                                                    props ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___35
                                                                    ->
                                                                    FStar_List_Tot_Base.flatten
                                                                    props))))
                                                                    uu___34)))
                                                                    uu___33)))
                                                                    uu___31)))
                                                                    uu___30)))
                                                                    uu___28)))
                                                                    uu___26)
                                                                    else
                                                                    (let uu___26
                                                                    =
                                                                    FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    "Ignoring the global parameters' types" in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (861))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (861))
                                                                    (Prims.of_int (65)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (862))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (862))
                                                                    (Prims.of_int (14)))))
                                                                    (Obj.magic
                                                                    uu___26)
                                                                    (fun
                                                                    uu___27
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___28
                                                                    -> []))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (822))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (864))
                                                                    (Prims.of_int (13)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (865))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (932))
                                                                    (Prims.of_int (62)))))
                                                                    (Obj.magic
                                                                    uu___24)
                                                                    (fun
                                                                    uu___25
                                                                    ->
                                                                    (fun
                                                                    gparams_props
                                                                    ->
                                                                    let uu___25
                                                                    =
                                                                    match 
                                                                    ((ei.ei_pre),
                                                                    with_gpre)
                                                                    with
                                                                    | 
                                                                    (FStar_Pervasives_Native.Some
                                                                    pre,
                                                                    true) ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___26
                                                                    =
                                                                    FStar_InteractiveHelpers_ExploreTerm.term_has_shadowed_variables
                                                                    ge1 pre in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (872))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (872))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (872))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (877))
                                                                    (Prims.of_int (26)))))
                                                                    (Obj.magic
                                                                    uu___26)
                                                                    (fun
                                                                    uu___27
                                                                    ->
                                                                    (fun
                                                                    uu___27
                                                                    ->
                                                                    if
                                                                    uu___27
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___28
                                                                    =
                                                                    FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    "Dropping the global precondition because of shadowed variables" in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (874))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (874))
                                                                    (Prims.of_int (92)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (875))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (875))
                                                                    (Prims.of_int (18)))))
                                                                    (Obj.magic
                                                                    uu___28)
                                                                    (fun
                                                                    uu___29
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___30
                                                                    ->
                                                                    FStar_Pervasives_Native.None))))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___29
                                                                    ->
                                                                    ei.ei_pre))))
                                                                    uu___27)))
                                                                    | 
                                                                    uu___26
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___27
                                                                    ->
                                                                    FStar_Pervasives_Native.None))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (870))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (878))
                                                                    (Prims.of_int (21)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (879))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (932))
                                                                    (Prims.of_int (62)))))
                                                                    (Obj.magic
                                                                    uu___25)
                                                                    (fun
                                                                    uu___26
                                                                    ->
                                                                    (fun gpre
                                                                    ->
                                                                    let uu___26
                                                                    =
                                                                    if
                                                                    Prims.op_Negation
                                                                    with_gpost
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___27
                                                                    ->
                                                                    (FStar_Pervasives_Native.None,
                                                                    []))))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (if
                                                                    is_let
                                                                    then
                                                                    let uu___28
                                                                    =
                                                                    FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    "Dropping the global postcondition and return type because we are studying a let expression" in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (886))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (886))
                                                                    (Prims.of_int (118)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (887))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (887))
                                                                    (Prims.of_int (20)))))
                                                                    (Obj.magic
                                                                    uu___28)
                                                                    (fun
                                                                    uu___29
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___30
                                                                    ->
                                                                    (FStar_Pervasives_Native.None,
                                                                    [])))
                                                                    else
                                                                    FStar_Tactics_V1_Derived.try_with
                                                                    (fun
                                                                    uu___29
                                                                    ->
                                                                    match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    let uu___30
                                                                    =
                                                                    FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    "> Generating propositions from the global type cast" in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (898))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (898))
                                                                    (Prims.of_int (81)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (899))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (906))
                                                                    (Prims.of_int (50)))))
                                                                    (Obj.magic
                                                                    uu___30)
                                                                    (fun
                                                                    uu___31
                                                                    ->
                                                                    (fun
                                                                    uu___31
                                                                    ->
                                                                    let uu___32
                                                                    =
                                                                    let uu___33
                                                                    =
                                                                    let uu___34
                                                                    =
                                                                    FStar_InteractiveHelpers_ExploreTerm.type_info_to_string
                                                                    einfo.ei_ret_type in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (899))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (899))
                                                                    (Prims.of_int (85)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___34)
                                                                    (fun
                                                                    uu___35
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___36
                                                                    ->
                                                                    Prims.strcat
                                                                    "- known type: "
                                                                    uu___35)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (899))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (899))
                                                                    (Prims.of_int (86)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (899))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (899))
                                                                    (Prims.of_int (86)))))
                                                                    (Obj.magic
                                                                    uu___33)
                                                                    (fun
                                                                    uu___34
                                                                    ->
                                                                    (fun
                                                                    uu___34
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    uu___34))
                                                                    uu___34) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (899))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (899))
                                                                    (Prims.of_int (86)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (900))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (906))
                                                                    (Prims.of_int (50)))))
                                                                    (Obj.magic
                                                                    uu___32)
                                                                    (fun
                                                                    uu___33
                                                                    ->
                                                                    (fun
                                                                    uu___33
                                                                    ->
                                                                    let uu___34
                                                                    =
                                                                    let uu___35
                                                                    =
                                                                    let uu___36
                                                                    =
                                                                    FStar_InteractiveHelpers_ExploreTerm.type_info_to_string
                                                                    ei.ei_ret_type in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (900))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (900))
                                                                    (Prims.of_int (82)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___36)
                                                                    (fun
                                                                    uu___37
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___38
                                                                    ->
                                                                    Prims.strcat
                                                                    "- exp. type : "
                                                                    uu___37)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (900))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (900))
                                                                    (Prims.of_int (83)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (900))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (900))
                                                                    (Prims.of_int (83)))))
                                                                    (Obj.magic
                                                                    uu___35)
                                                                    (fun
                                                                    uu___36
                                                                    ->
                                                                    (fun
                                                                    uu___36
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    uu___36))
                                                                    uu___36) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (900))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (900))
                                                                    (Prims.of_int (83)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (900))
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (906))
                                                                    (Prims.of_int (50)))))
                                                                    (Obj.magic
                                                                    uu___34)
                                                                    (fun
                                                                    uu___35
                                                                    ->
                                                                    (fun
                                                                    uu___35
                                                                    ->
                                                                    let uu___36
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___37
                                                                    ->
                                                                    mk_cast_info
                                                                    v1
                                                                    (FStar_Pervasives_Native.Some
                                                                    (einfo.ei_ret_type))
                                                                    (FStar_Pervasives_Native.Some
                                                                    (ei.ei_ret_type)))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (901))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (901))
                                                                    (Prims.of_int (87)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (902))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (906))
                                                                    (Prims.of_int (50)))))
                                                                    (Obj.magic
                                                                    uu___36)
                                                                    (fun
                                                                    uu___37
                                                                    ->
                                                                    (fun
                                                                    gcast ->
                                                                    let uu___37
                                                                    =
                                                                    let uu___38
                                                                    =
                                                                    cast_info_to_string
                                                                    gcast in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (902))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (902))
                                                                    (Prims.of_int (55)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (902))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (902))
                                                                    (Prims.of_int (55)))))
                                                                    (Obj.magic
                                                                    uu___38)
                                                                    (fun
                                                                    uu___39
                                                                    ->
                                                                    (fun
                                                                    uu___39
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    uu___39))
                                                                    uu___39) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (902))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (902))
                                                                    (Prims.of_int (55)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (902))
                                                                    (Prims.of_int (56))
                                                                    (Prims.of_int (906))
                                                                    (Prims.of_int (50)))))
                                                                    (Obj.magic
                                                                    uu___37)
                                                                    (fun
                                                                    uu___38
                                                                    ->
                                                                    (fun
                                                                    uu___38
                                                                    ->
                                                                    let uu___39
                                                                    =
                                                                    cast_info_to_propositions
                                                                    dbg ge1
                                                                    gcast in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (903))
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (903))
                                                                    (Prims.of_int (71)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (904))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (906))
                                                                    (Prims.of_int (50)))))
                                                                    (Obj.magic
                                                                    uu___39)
                                                                    (fun
                                                                    uu___40
                                                                    ->
                                                                    (fun
                                                                    gcast_props
                                                                    ->
                                                                    let uu___40
                                                                    =
                                                                    FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    "> Propositions for global type cast:" in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (904))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (904))
                                                                    (Prims.of_int (66)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (905))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (906))
                                                                    (Prims.of_int (50)))))
                                                                    (Obj.magic
                                                                    uu___40)
                                                                    (fun
                                                                    uu___41
                                                                    ->
                                                                    (fun
                                                                    uu___41
                                                                    ->
                                                                    let uu___42
                                                                    =
                                                                    let uu___43
                                                                    =
                                                                    FStar_InteractiveHelpers_Base.list_to_string
                                                                    FStarC_Tactics_V1_Builtins.term_to_string
                                                                    gcast_props in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (905))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (905))
                                                                    (Prims.of_int (71)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (905))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (905))
                                                                    (Prims.of_int (71)))))
                                                                    (Obj.magic
                                                                    uu___43)
                                                                    (fun
                                                                    uu___44
                                                                    ->
                                                                    (fun
                                                                    uu___44
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    uu___44))
                                                                    uu___44) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (905))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (905))
                                                                    (Prims.of_int (71)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (906))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (906))
                                                                    (Prims.of_int (50)))))
                                                                    (Obj.magic
                                                                    uu___42)
                                                                    (fun
                                                                    uu___43
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___44
                                                                    ->
                                                                    ((ei.ei_post),
                                                                    (FStar_List_Tot_Base.rev
                                                                    gcast_props))))))
                                                                    uu___41)))
                                                                    uu___40)))
                                                                    uu___38)))
                                                                    uu___37)))
                                                                    uu___35)))
                                                                    uu___33)))
                                                                    uu___31))
                                                                    (fun
                                                                    uu___29
                                                                    ->
                                                                    let uu___30
                                                                    =
                                                                    FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    "Dropping the global postcondition and return type because of incoherent typing" in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (909))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (909))
                                                                    (Prims.of_int (108)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (910))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (910))
                                                                    (Prims.of_int (22)))))
                                                                    (Obj.magic
                                                                    uu___30)
                                                                    (fun
                                                                    uu___31
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___32
                                                                    ->
                                                                    (FStar_Pervasives_Native.None,
                                                                    [])))))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (883))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (910))
                                                                    (Prims.of_int (22)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (879))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (932))
                                                                    (Prims.of_int (62)))))
                                                                    (Obj.magic
                                                                    uu___26)
                                                                    (fun
                                                                    uu___27
                                                                    ->
                                                                    (fun
                                                                    uu___27
                                                                    ->
                                                                    match uu___27
                                                                    with
                                                                    | 
                                                                    (gpost,
                                                                    gcast_props)
                                                                    ->
                                                                    let uu___28
                                                                    =
                                                                    FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    "> Instantiating global pre/post" in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (914))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (914))
                                                                    (Prims.of_int (55)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (914))
                                                                    (Prims.of_int (56))
                                                                    (Prims.of_int (932))
                                                                    (Prims.of_int (62)))))
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
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___31
                                                                    ->
                                                                    if is_let
                                                                    then
                                                                    FStar_List_Tot_Base.rev
                                                                    children
                                                                    else
                                                                    if
                                                                    effect_type_is_stateful
                                                                    einfo.ei_type
                                                                    then
                                                                    FStar_List_Tot_Base.rev
                                                                    children
                                                                    else
                                                                    parents)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (921))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (923))
                                                                    (Prims.of_int (22)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (924))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (932))
                                                                    (Prims.of_int (62)))))
                                                                    (Obj.magic
                                                                    uu___30)
                                                                    (fun
                                                                    uu___31
                                                                    ->
                                                                    (fun
                                                                    gchildren
                                                                    ->
                                                                    let uu___31
                                                                    =
                                                                    pre_post_to_propositions
                                                                    dbg ge1
                                                                    ei.ei_type
                                                                    v1 opt_b
                                                                    einfo.ei_ret_type
                                                                    gpre
                                                                    gpost
                                                                    (FStar_List_Tot_Base.rev
                                                                    parents)
                                                                    gchildren in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (926))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (927))
                                                                    (Prims.of_int (69)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (924))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (932))
                                                                    (Prims.of_int (62)))))
                                                                    (Obj.magic
                                                                    uu___31)
                                                                    (fun
                                                                    uu___32
                                                                    ->
                                                                    (fun
                                                                    uu___32
                                                                    ->
                                                                    match uu___32
                                                                    with
                                                                    | 
                                                                    (ge2,
                                                                    gpre_prop,
                                                                    gpost_prop)
                                                                    ->
                                                                    let uu___33
                                                                    =
                                                                    let uu___34
                                                                    =
                                                                    let uu___35
                                                                    =
                                                                    FStar_InteractiveHelpers_Base.option_to_string
                                                                    FStarC_Tactics_V1_Builtins.term_to_string
                                                                    gpre_prop in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (929))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (929))
                                                                    (Prims.of_int (88)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___35)
                                                                    (fun
                                                                    uu___36
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___37
                                                                    ->
                                                                    Prims.strcat
                                                                    "- global pre prop: "
                                                                    uu___36)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (929))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (929))
                                                                    (Prims.of_int (89)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (929))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (929))
                                                                    (Prims.of_int (89)))))
                                                                    (Obj.magic
                                                                    uu___34)
                                                                    (fun
                                                                    uu___35
                                                                    ->
                                                                    (fun
                                                                    uu___35
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    uu___35))
                                                                    uu___35) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (929))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (929))
                                                                    (Prims.of_int (89)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (930))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (932))
                                                                    (Prims.of_int (62)))))
                                                                    (Obj.magic
                                                                    uu___33)
                                                                    (fun
                                                                    uu___34
                                                                    ->
                                                                    (fun
                                                                    uu___34
                                                                    ->
                                                                    let uu___35
                                                                    =
                                                                    let uu___36
                                                                    =
                                                                    let uu___37
                                                                    =
                                                                    FStar_InteractiveHelpers_Base.option_to_string
                                                                    FStarC_Tactics_V1_Builtins.term_to_string
                                                                    gpost_prop in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (930))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (930))
                                                                    (Prims.of_int (90)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___37)
                                                                    (fun
                                                                    uu___38
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___39
                                                                    ->
                                                                    Prims.strcat
                                                                    "- global post prop: "
                                                                    uu___38)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (930))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (930))
                                                                    (Prims.of_int (91)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (930))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (930))
                                                                    (Prims.of_int (91)))))
                                                                    (Obj.magic
                                                                    uu___36)
                                                                    (fun
                                                                    uu___37
                                                                    ->
                                                                    (fun
                                                                    uu___37
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    uu___37))
                                                                    uu___37) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (930))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (930))
                                                                    (Prims.of_int (91)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (932))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (932))
                                                                    (Prims.of_int (62)))))
                                                                    (Obj.magic
                                                                    uu___35)
                                                                    (fun
                                                                    uu___36
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___37
                                                                    ->
                                                                    (ge2,
                                                                    gparams_props,
                                                                    gpre_prop,
                                                                    gcast_props,
                                                                    gpost_prop)))))
                                                                    uu___34)))
                                                                    uu___32)))
                                                                    uu___31)))
                                                                    uu___29)))
                                                                    uu___27)))
                                                                    uu___26)))
                                                                    uu___25)))
                                                                    uu___23)))
                                                                    uu___21)))
                                                                    uu___19)))
                                                                    uu___18)))
                                                                    | 
                                                                    (uu___17,
                                                                    uu___18)
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    (ge1, [],
                                                                    FStar_Pervasives_Native.None,
                                                                    [],
                                                                    FStar_Pervasives_Native.None)))))
                                                                    uu___17) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (808))
                                                                    (Prims.of_int (64))
                                                                    (Prims.of_int (935))
                                                                    (Prims.of_int (18)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (806))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (961))
                                                                    (Prims.of_int (39)))))
                                                                    (Obj.magic
                                                                    uu___15)
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    match uu___16
                                                                    with
                                                                    | 
                                                                    (ge2,
                                                                    gparams_props,
                                                                    gpre_prop,
                                                                    gcast_props,
                                                                    gpost_prop)
                                                                    ->
                                                                    let uu___17
                                                                    =
                                                                    cast_info_list_to_propositions
                                                                    dbg ge2
                                                                    info.parameters in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (939))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (939))
                                                                    (Prims.of_int (77)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (939))
                                                                    (Prims.of_int (80))
                                                                    (Prims.of_int (961))
                                                                    (Prims.of_int (39)))))
                                                                    (Obj.magic
                                                                    uu___17)
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    (fun
                                                                    params_props
                                                                    ->
                                                                    let uu___18
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    if
                                                                    FStar_InteractiveHelpers_ExploreTerm.uu___is_E_Lemma
                                                                    einfo.ei_type
                                                                    then
                                                                    ([], [])
                                                                    else
                                                                    ([v1],
                                                                    ((match opt_b
                                                                    with
                                                                    | FStar_Pervasives_Native.Some
                                                                    b -> 
                                                                    [b]
                                                                    | FStar_Pervasives_Native.None
                                                                    -> []))))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (942))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (943))
                                                                    (Prims.of_int (63)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (939))
                                                                    (Prims.of_int (80))
                                                                    (Prims.of_int (961))
                                                                    (Prims.of_int (39)))))
                                                                    (Obj.magic
                                                                    uu___18)
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    match uu___19
                                                                    with
                                                                    | 
                                                                    (ret_values,
                                                                    ret_binders)
                                                                    ->
                                                                    let uu___20
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___21
                                                                    ->
                                                                    ret_values)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (943))
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (961))
                                                                    (Prims.of_int (39)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (943))
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (961))
                                                                    (Prims.of_int (39)))))
                                                                    (Obj.magic
                                                                    uu___20)
                                                                    (fun
                                                                    uu___21
                                                                    ->
                                                                    (fun
                                                                    ret_values1
                                                                    ->
                                                                    let uu___21
                                                                    =
                                                                    match ret_values1
                                                                    with
                                                                    | 
                                                                    v2::[] ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___22
                                                                    =
                                                                    mk_has_type
                                                                    v2
                                                                    (einfo.ei_ret_type).FStar_InteractiveHelpers_ExploreTerm.ty in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (946))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (946))
                                                                    (Prims.of_int (56)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (946))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (946))
                                                                    (Prims.of_int (56)))))
                                                                    (Obj.magic
                                                                    uu___22)
                                                                    (fun
                                                                    uu___23
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___24
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___23))))
                                                                    | 
                                                                    uu___22
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___23
                                                                    ->
                                                                    FStar_Pervasives_Native.None))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (945))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (947))
                                                                    (Prims.of_int (17)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (948))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (961))
                                                                    (Prims.of_int (39)))))
                                                                    (Obj.magic
                                                                    uu___21)
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    (fun
                                                                    ret_has_type_prop
                                                                    ->
                                                                    let uu___22
                                                                    =
                                                                    FStar_InteractiveHelpers_Base.opt_mk_app_norm
                                                                    ge2.FStar_InteractiveHelpers_Base.env
                                                                    (get_opt_refinment
                                                                    einfo.ei_ret_type)
                                                                    ret_values1 in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (949))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (949))
                                                                    (Prims.of_int (97)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (949))
                                                                    (Prims.of_int (100))
                                                                    (Prims.of_int (961))
                                                                    (Prims.of_int (39)))))
                                                                    (Obj.magic
                                                                    uu___22)
                                                                    (fun
                                                                    uu___23
                                                                    ->
                                                                    (fun
                                                                    ret_refin_prop
                                                                    ->
                                                                    let uu___23
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___24
                                                                    ->
                                                                    FStar_InteractiveHelpers_Base.opt_cons
                                                                    gpre_prop
                                                                    (FStar_List_Tot_Base.append
                                                                    params_props
                                                                    (FStar_InteractiveHelpers_Base.opt_cons
                                                                    pre_prop
                                                                    [])))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (951))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (951))
                                                                    (Prims.of_int (87)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (951))
                                                                    (Prims.of_int (90))
                                                                    (Prims.of_int (961))
                                                                    (Prims.of_int (39)))))
                                                                    (Obj.magic
                                                                    uu___23)
                                                                    (fun
                                                                    uu___24
                                                                    ->
                                                                    (fun pres
                                                                    ->
                                                                    let uu___24
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___25
                                                                    ->
                                                                    FStar_List_Tot_Base.append
                                                                    gparams_props
                                                                    pres)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (952))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (952))
                                                                    (Prims.of_int (40)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (952))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (961))
                                                                    (Prims.of_int (39)))))
                                                                    (Obj.magic
                                                                    uu___24)
                                                                    (fun
                                                                    uu___25
                                                                    ->
                                                                    (fun
                                                                    pres1 ->
                                                                    let uu___25
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___26
                                                                    ->
                                                                    FStar_InteractiveHelpers_Base.opt_cons
                                                                    ret_has_type_prop
                                                                    (FStar_InteractiveHelpers_Base.opt_cons
                                                                    ret_refin_prop
                                                                    (FStar_InteractiveHelpers_Base.opt_cons
                                                                    post_prop
                                                                    (FStar_List_Tot_Base.append
                                                                    gcast_props
                                                                    (FStar_InteractiveHelpers_Base.opt_cons
                                                                    gpost_prop
                                                                    [])))))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (953))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (955))
                                                                    (Prims.of_int (73)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (957))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (961))
                                                                    (Prims.of_int (39)))))
                                                                    (Obj.magic
                                                                    uu___25)
                                                                    (fun
                                                                    uu___26
                                                                    ->
                                                                    (fun
                                                                    posts ->
                                                                    let uu___26
                                                                    =
                                                                    FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    "- generated pres:" in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (957))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (957))
                                                                    (Prims.of_int (37)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (958))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (961))
                                                                    (Prims.of_int (39)))))
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
                                                                    if dbg
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Util.iter
                                                                    (fun x ->
                                                                    let uu___29
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.term_to_string
                                                                    x in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (958))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (958))
                                                                    (Prims.of_int (55)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (958))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (958))
                                                                    (Prims.of_int (55)))))
                                                                    (Obj.magic
                                                                    uu___29)
                                                                    (fun
                                                                    uu___30
                                                                    ->
                                                                    (fun
                                                                    uu___30
                                                                    ->
                                                                    Obj.magic
                                                                    (FStarC_Tactics_V1_Builtins.print
                                                                    uu___30))
                                                                    uu___30))
                                                                    pres1))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___30
                                                                    -> ()))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (958))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (958))
                                                                    (Prims.of_int (61)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (959))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (961))
                                                                    (Prims.of_int (39)))))
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
                                                                    FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    "- generated posts:" in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (959))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (959))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (960))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (961))
                                                                    (Prims.of_int (39)))))
                                                                    (Obj.magic
                                                                    uu___30)
                                                                    (fun
                                                                    uu___31
                                                                    ->
                                                                    (fun
                                                                    uu___31
                                                                    ->
                                                                    let uu___32
                                                                    =
                                                                    if dbg
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Util.iter
                                                                    (fun x ->
                                                                    let uu___33
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.term_to_string
                                                                    x in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (960))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (960))
                                                                    (Prims.of_int (55)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (960))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (960))
                                                                    (Prims.of_int (55)))))
                                                                    (Obj.magic
                                                                    uu___33)
                                                                    (fun
                                                                    uu___34
                                                                    ->
                                                                    (fun
                                                                    uu___34
                                                                    ->
                                                                    Obj.magic
                                                                    (FStarC_Tactics_V1_Builtins.print
                                                                    uu___34))
                                                                    uu___34))
                                                                    posts))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___34
                                                                    -> ()))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (960))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (960))
                                                                    (Prims.of_int (62)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (961))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (961))
                                                                    (Prims.of_int (39)))))
                                                                    (Obj.magic
                                                                    uu___32)
                                                                    (fun
                                                                    uu___33
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___34
                                                                    ->
                                                                    (ge2,
                                                                    {
                                                                    FStar_InteractiveHelpers_Propositions.pres
                                                                    = pres1;
                                                                    FStar_InteractiveHelpers_Propositions.posts
                                                                    = posts
                                                                    })))))
                                                                    uu___31)))
                                                                    uu___29)))
                                                                    uu___27)))
                                                                    uu___26)))
                                                                    uu___25)))
                                                                    uu___24)))
                                                                    uu___23)))
                                                                    uu___22)))
                                                                    uu___21)))
                                                                    uu___19)))
                                                                    uu___18)))
                                                                    uu___16))))
                                                                    uu___13)))
                                                                    uu___11)))
                                                                    uu___9)))
                                                                    uu___7)))
                                                                    uu___6)))
                                                       uu___4))) uu___3)))
                                 uu___1)