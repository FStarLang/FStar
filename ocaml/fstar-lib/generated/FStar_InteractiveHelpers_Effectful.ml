open Prims
let (term_eq :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term ->
      (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  = FStar_Tactics_Builtins.term_eq_old
type cast_info =
  {
  term: FStar_Reflection_Types.term ;
  p_ty:
    FStar_InteractiveHelpers_ExploreTerm.type_info
      FStar_Pervasives_Native.option
    ;
  exp_ty:
    FStar_InteractiveHelpers_ExploreTerm.type_info
      FStar_Pervasives_Native.option
    }
let (__proj__Mkcast_info__item__term :
  cast_info -> FStar_Reflection_Types.term) =
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
  FStar_Reflection_Types.term ->
    FStar_InteractiveHelpers_ExploreTerm.type_info
      FStar_Pervasives_Native.option ->
      FStar_InteractiveHelpers_ExploreTerm.type_info
        FStar_Pervasives_Native.option -> cast_info)
  = fun t -> fun p_ty -> fun exp_ty -> { term = t; p_ty; exp_ty }
let (cast_info_to_string :
  cast_info -> (Prims.string, unit) FStar_Tactics_Effect.tac_repr) =
  fun info ->
    FStar_Tactics_Effect.tac_bind
      (Prims.mk_range "FStar.InteractiveHelpers.Effectful.fst"
         (Prims.of_int (33)) (Prims.of_int (20)) (Prims.of_int (35))
         (Prims.of_int (56)))
      (Prims.mk_range "prims.fst" (Prims.of_int (606)) (Prims.of_int (19))
         (Prims.of_int (606)) (Prims.of_int (31)))
      (Obj.magic
         (FStar_Tactics_Effect.tac_bind
            (Prims.mk_range "FStar.InteractiveHelpers.Effectful.fst"
               (Prims.of_int (33)) (Prims.of_int (20)) (Prims.of_int (33))
               (Prims.of_int (44)))
            (Prims.mk_range "FStar.InteractiveHelpers.Effectful.fst"
               (Prims.of_int (33)) (Prims.of_int (20)) (Prims.of_int (35))
               (Prims.of_int (56)))
            (Obj.magic (FStar_Tactics_Builtins.term_to_string info.term))
            (fun uu___ ->
               (fun uu___ ->
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (Prims.mk_range
                          "FStar.InteractiveHelpers.Effectful.fst"
                          (Prims.of_int (33)) (Prims.of_int (47))
                          (Prims.of_int (35)) (Prims.of_int (56)))
                       (Prims.mk_range "prims.fst" (Prims.of_int (606))
                          (Prims.of_int (19)) (Prims.of_int (606))
                          (Prims.of_int (31)))
                       (Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (Prims.mk_range
                                "FStar.InteractiveHelpers.Effectful.fst"
                                (Prims.of_int (34)) (Prims.of_int (2))
                                (Prims.of_int (35)) (Prims.of_int (56)))
                             (Prims.mk_range "prims.fst" (Prims.of_int (606))
                                (Prims.of_int (19)) (Prims.of_int (606))
                                (Prims.of_int (31)))
                             (Obj.magic
                                (FStar_Tactics_Effect.tac_bind
                                   (Prims.mk_range
                                      "FStar.InteractiveHelpers.Effectful.fst"
                                      (Prims.of_int (34)) (Prims.of_int (2))
                                      (Prims.of_int (34)) (Prims.of_int (48)))
                                   (Prims.mk_range
                                      "FStar.InteractiveHelpers.Effectful.fst"
                                      (Prims.of_int (34)) (Prims.of_int (2))
                                      (Prims.of_int (35)) (Prims.of_int (56)))
                                   (Obj.magic
                                      (FStar_InteractiveHelpers_Base.option_to_string
                                         FStar_InteractiveHelpers_ExploreTerm.type_info_to_string
                                         info.p_ty))
                                   (fun uu___1 ->
                                      (fun uu___1 ->
                                         Obj.magic
                                           (FStar_Tactics_Effect.tac_bind
                                              (Prims.mk_range
                                                 "FStar.InteractiveHelpers.Effectful.fst"
                                                 (Prims.of_int (34))
                                                 (Prims.of_int (51))
                                                 (Prims.of_int (35))
                                                 (Prims.of_int (56)))
                                              (Prims.mk_range "prims.fst"
                                                 (Prims.of_int (606))
                                                 (Prims.of_int (19))
                                                 (Prims.of_int (606))
                                                 (Prims.of_int (31)))
                                              (Obj.magic
                                                 (FStar_Tactics_Effect.tac_bind
                                                    (Prims.mk_range
                                                       "FStar.InteractiveHelpers.Effectful.fst"
                                                       (Prims.of_int (35))
                                                       (Prims.of_int (2))
                                                       (Prims.of_int (35))
                                                       (Prims.of_int (56)))
                                                    (Prims.mk_range
                                                       "prims.fst"
                                                       (Prims.of_int (606))
                                                       (Prims.of_int (19))
                                                       (Prims.of_int (606))
                                                       (Prims.of_int (31)))
                                                    (Obj.magic
                                                       (FStar_Tactics_Effect.tac_bind
                                                          (Prims.mk_range
                                                             "FStar.InteractiveHelpers.Effectful.fst"
                                                             (Prims.of_int (35))
                                                             (Prims.of_int (2))
                                                             (Prims.of_int (35))
                                                             (Prims.of_int (50)))
                                                          (Prims.mk_range
                                                             "prims.fst"
                                                             (Prims.of_int (606))
                                                             (Prims.of_int (19))
                                                             (Prims.of_int (606))
                                                             (Prims.of_int (31)))
                                                          (Obj.magic
                                                             (FStar_InteractiveHelpers_Base.option_to_string
                                                                FStar_InteractiveHelpers_ExploreTerm.type_info_to_string
                                                                info.exp_ty))
                                                          (fun uu___2 ->
                                                             FStar_Tactics_Effect.lift_div_tac
                                                               (fun uu___3 ->
                                                                  Prims.strcat
                                                                    uu___2
                                                                    ")"))))
                                                    (fun uu___2 ->
                                                       FStar_Tactics_Effect.lift_div_tac
                                                         (fun uu___3 ->
                                                            Prims.strcat
                                                              ") (" uu___2))))
                                              (fun uu___2 ->
                                                 FStar_Tactics_Effect.lift_div_tac
                                                   (fun uu___3 ->
                                                      Prims.strcat uu___1
                                                        uu___2)))) uu___1)))
                             (fun uu___1 ->
                                FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___2 -> Prims.strcat ") (" uu___1))))
                       (fun uu___1 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___2 -> Prims.strcat uu___ uu___1))))
                 uu___)))
      (fun uu___ ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___1 -> Prims.strcat "Mkcast_info (" uu___))
type effect_info =
  {
  ei_type: FStar_InteractiveHelpers_ExploreTerm.effect_type ;
  ei_ret_type: FStar_InteractiveHelpers_ExploreTerm.type_info ;
  ei_pre: FStar_Reflection_Types.term FStar_Pervasives_Native.option ;
  ei_post: FStar_Reflection_Types.term FStar_Pervasives_Native.option }
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
  effect_info -> FStar_Reflection_Types.term FStar_Pervasives_Native.option)
  =
  fun projectee ->
    match projectee with
    | { ei_type; ei_ret_type; ei_pre; ei_post;_} -> ei_pre
let (__proj__Mkeffect_info__item__ei_post :
  effect_info -> FStar_Reflection_Types.term FStar_Pervasives_Native.option)
  =
  fun projectee ->
    match projectee with
    | { ei_type; ei_ret_type; ei_pre; ei_post;_} -> ei_post
let (mk_effect_info :
  FStar_InteractiveHelpers_ExploreTerm.effect_type ->
    FStar_InteractiveHelpers_ExploreTerm.type_info ->
      FStar_Reflection_Types.term FStar_Pervasives_Native.option ->
        FStar_Reflection_Types.term FStar_Pervasives_Native.option ->
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
    FStar_Tactics_Effect.tac_bind
      (Prims.mk_range "FStar.InteractiveHelpers.Effectful.fst"
         (Prims.of_int (51)) (Prims.of_int (2)) (Prims.of_int (54))
         (Prims.of_int (49)))
      (Prims.mk_range "prims.fst" (Prims.of_int (606)) (Prims.of_int (19))
         (Prims.of_int (606)) (Prims.of_int (31)))
      (Obj.magic
         (FStar_Tactics_Effect.tac_bind
            (Prims.mk_range "FStar.InteractiveHelpers.Effectful.fst"
               (Prims.of_int (51)) (Prims.of_int (36)) (Prims.of_int (54))
               (Prims.of_int (49)))
            (Prims.mk_range "prims.fst" (Prims.of_int (606))
               (Prims.of_int (19)) (Prims.of_int (606)) (Prims.of_int (31)))
            (Obj.magic
               (FStar_Tactics_Effect.tac_bind
                  (Prims.mk_range "FStar.InteractiveHelpers.Effectful.fst"
                     (Prims.of_int (52)) (Prims.of_int (2))
                     (Prims.of_int (54)) (Prims.of_int (49)))
                  (Prims.mk_range "prims.fst" (Prims.of_int (606))
                     (Prims.of_int (19)) (Prims.of_int (606))
                     (Prims.of_int (31)))
                  (Obj.magic
                     (FStar_Tactics_Effect.tac_bind
                        (Prims.mk_range
                           "FStar.InteractiveHelpers.Effectful.fst"
                           (Prims.of_int (52)) (Prims.of_int (2))
                           (Prims.of_int (52)) (Prims.of_int (42)))
                        (Prims.mk_range
                           "FStar.InteractiveHelpers.Effectful.fst"
                           (Prims.of_int (52)) (Prims.of_int (2))
                           (Prims.of_int (54)) (Prims.of_int (49)))
                        (Obj.magic
                           (FStar_InteractiveHelpers_Base.option_to_string
                              FStar_Tactics_Builtins.term_to_string c.ei_pre))
                        (fun uu___ ->
                           (fun uu___ ->
                              Obj.magic
                                (FStar_Tactics_Effect.tac_bind
                                   (Prims.mk_range
                                      "FStar.InteractiveHelpers.Effectful.fst"
                                      (Prims.of_int (52)) (Prims.of_int (45))
                                      (Prims.of_int (54)) (Prims.of_int (49)))
                                   (Prims.mk_range "prims.fst"
                                      (Prims.of_int (606))
                                      (Prims.of_int (19))
                                      (Prims.of_int (606))
                                      (Prims.of_int (31)))
                                   (Obj.magic
                                      (FStar_Tactics_Effect.tac_bind
                                         (Prims.mk_range
                                            "FStar.InteractiveHelpers.Effectful.fst"
                                            (Prims.of_int (53))
                                            (Prims.of_int (2))
                                            (Prims.of_int (54))
                                            (Prims.of_int (49)))
                                         (Prims.mk_range "prims.fst"
                                            (Prims.of_int (606))
                                            (Prims.of_int (19))
                                            (Prims.of_int (606))
                                            (Prims.of_int (31)))
                                         (Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (Prims.mk_range
                                                  "FStar.InteractiveHelpers.Effectful.fst"
                                                  (Prims.of_int (53))
                                                  (Prims.of_int (2))
                                                  (Prims.of_int (53))
                                                  (Prims.of_int (35)))
                                               (Prims.mk_range
                                                  "FStar.InteractiveHelpers.Effectful.fst"
                                                  (Prims.of_int (53))
                                                  (Prims.of_int (2))
                                                  (Prims.of_int (54))
                                                  (Prims.of_int (49)))
                                               (Obj.magic
                                                  (FStar_InteractiveHelpers_ExploreTerm.type_info_to_string
                                                     c.ei_ret_type))
                                               (fun uu___1 ->
                                                  (fun uu___1 ->
                                                     Obj.magic
                                                       (FStar_Tactics_Effect.tac_bind
                                                          (Prims.mk_range
                                                             "FStar.InteractiveHelpers.Effectful.fst"
                                                             (Prims.of_int (53))
                                                             (Prims.of_int (38))
                                                             (Prims.of_int (54))
                                                             (Prims.of_int (49)))
                                                          (Prims.mk_range
                                                             "prims.fst"
                                                             (Prims.of_int (606))
                                                             (Prims.of_int (19))
                                                             (Prims.of_int (606))
                                                             (Prims.of_int (31)))
                                                          (Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (Prims.mk_range
                                                                   "FStar.InteractiveHelpers.Effectful.fst"
                                                                   (Prims.of_int (54))
                                                                   (Prims.of_int (2))
                                                                   (Prims.of_int (54))
                                                                   (Prims.of_int (49)))
                                                                (Prims.mk_range
                                                                   "prims.fst"
                                                                   (Prims.of_int (606))
                                                                   (Prims.of_int (19))
                                                                   (Prims.of_int (606))
                                                                   (Prims.of_int (31)))
                                                                (Obj.magic
                                                                   (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (43)))
                                                                    (Prims.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.option_to_string
                                                                    FStar_Tactics_Builtins.term_to_string
                                                                    c.ei_post))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Prims.strcat
                                                                    uu___2
                                                                    ")"))))
                                                                (fun uu___2
                                                                   ->
                                                                   FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Prims.strcat
                                                                    ") ("
                                                                    uu___2))))
                                                          (fun uu___2 ->
                                                             FStar_Tactics_Effect.lift_div_tac
                                                               (fun uu___3 ->
                                                                  Prims.strcat
                                                                    uu___1
                                                                    uu___2))))
                                                    uu___1)))
                                         (fun uu___1 ->
                                            FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___2 ->
                                                 Prims.strcat ") (" uu___1))))
                                   (fun uu___1 ->
                                      FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___2 ->
                                           Prims.strcat uu___ uu___1))))
                             uu___)))
                  (fun uu___ ->
                     FStar_Tactics_Effect.lift_div_tac
                       (fun uu___1 -> Prims.strcat " (" uu___))))
            (fun uu___ ->
               FStar_Tactics_Effect.lift_div_tac
                 (fun uu___1 ->
                    Prims.strcat
                      (FStar_InteractiveHelpers_ExploreTerm.effect_type_to_string
                         c.ei_type) uu___))))
      (fun uu___ ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___1 -> Prims.strcat "Mkeffect_info " uu___))
type eterm_info =
  {
  einfo: effect_info ;
  head: FStar_Reflection_Types.term ;
  parameters: cast_info Prims.list }
let (__proj__Mketerm_info__item__einfo : eterm_info -> effect_info) =
  fun projectee ->
    match projectee with | { einfo; head; parameters;_} -> einfo
let (__proj__Mketerm_info__item__head :
  eterm_info -> FStar_Reflection_Types.term) =
  fun projectee ->
    match projectee with | { einfo; head; parameters;_} -> head
let (__proj__Mketerm_info__item__parameters :
  eterm_info -> cast_info Prims.list) =
  fun projectee ->
    match projectee with | { einfo; head; parameters;_} -> parameters
let (eterm_info_to_string :
  eterm_info -> (Prims.string, unit) FStar_Tactics_Effect.tac_repr) =
  fun info ->
    FStar_Tactics_Effect.tac_bind
      (Prims.mk_range "FStar.InteractiveHelpers.Effectful.fst"
         (Prims.of_int (66)) (Prims.of_int (15)) (Prims.of_int (66))
         (Prims.of_int (84)))
      (Prims.mk_range "FStar.InteractiveHelpers.Effectful.fst"
         (Prims.of_int (67)) (Prims.of_int (2)) (Prims.of_int (71))
         (Prims.of_int (18)))
      (Obj.magic
         (FStar_Tactics_Util.map
            (fun x ->
               FStar_Tactics_Effect.tac_bind
                 (Prims.mk_range "FStar.InteractiveHelpers.Effectful.fst"
                    (Prims.of_int (66)) (Prims.of_int (35))
                    (Prims.of_int (66)) (Prims.of_int (67)))
                 (Prims.mk_range "prims.fst" (Prims.of_int (606))
                    (Prims.of_int (19)) (Prims.of_int (606))
                    (Prims.of_int (31)))
                 (Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (Prims.mk_range
                          "FStar.InteractiveHelpers.Effectful.fst"
                          (Prims.of_int (66)) (Prims.of_int (35))
                          (Prims.of_int (66)) (Prims.of_int (56)))
                       (Prims.mk_range "prims.fst" (Prims.of_int (606))
                          (Prims.of_int (19)) (Prims.of_int (606))
                          (Prims.of_int (31)))
                       (Obj.magic (cast_info_to_string x))
                       (fun uu___ ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___1 -> Prims.strcat uu___ ");  \n"))))
                 (fun uu___ ->
                    FStar_Tactics_Effect.lift_div_tac
                      (fun uu___1 -> Prims.strcat "(" uu___)))
            info.parameters))
      (fun uu___ ->
         (fun params ->
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (Prims.mk_range "FStar.InteractiveHelpers.Effectful.fst"
                    (Prims.of_int (67)) (Prims.of_int (19))
                    (Prims.of_int (67)) (Prims.of_int (66)))
                 (Prims.mk_range "FStar.InteractiveHelpers.Effectful.fst"
                    (Prims.of_int (68)) (Prims.of_int (2))
                    (Prims.of_int (71)) (Prims.of_int (18)))
                 (FStar_Tactics_Effect.lift_div_tac
                    (fun uu___ ->
                       FStar_List_Tot_Base.fold_left
                         (fun x -> fun y -> Prims.strcat x y) "" params))
                 (fun uu___ ->
                    (fun params_str ->
                       Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (Prims.mk_range
                               "FStar.InteractiveHelpers.Effectful.fst"
                               (Prims.of_int (69)) (Prims.of_int (2))
                               (Prims.of_int (71)) (Prims.of_int (18)))
                            (Prims.mk_range "prims.fst" (Prims.of_int (606))
                               (Prims.of_int (19)) (Prims.of_int (606))
                               (Prims.of_int (31)))
                            (Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (Prims.mk_range
                                     "FStar.InteractiveHelpers.Effectful.fst"
                                     (Prims.of_int (69)) (Prims.of_int (2))
                                     (Prims.of_int (69)) (Prims.of_int (34)))
                                  (Prims.mk_range
                                     "FStar.InteractiveHelpers.Effectful.fst"
                                     (Prims.of_int (69)) (Prims.of_int (2))
                                     (Prims.of_int (71)) (Prims.of_int (18)))
                                  (Obj.magic
                                     (effect_info_to_string info.einfo))
                                  (fun uu___ ->
                                     (fun uu___ ->
                                        Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (Prims.mk_range
                                                "FStar.InteractiveHelpers.Effectful.fst"
                                                (Prims.of_int (69))
                                                (Prims.of_int (37))
                                                (Prims.of_int (71))
                                                (Prims.of_int (18)))
                                             (Prims.mk_range "prims.fst"
                                                (Prims.of_int (606))
                                                (Prims.of_int (19))
                                                (Prims.of_int (606))
                                                (Prims.of_int (31)))
                                             (Obj.magic
                                                (FStar_Tactics_Effect.tac_bind
                                                   (Prims.mk_range
                                                      "FStar.InteractiveHelpers.Effectful.fst"
                                                      (Prims.of_int (70))
                                                      (Prims.of_int (2))
                                                      (Prims.of_int (71))
                                                      (Prims.of_int (18)))
                                                   (Prims.mk_range
                                                      "prims.fst"
                                                      (Prims.of_int (606))
                                                      (Prims.of_int (19))
                                                      (Prims.of_int (606))
                                                      (Prims.of_int (31)))
                                                   (Obj.magic
                                                      (FStar_Tactics_Effect.tac_bind
                                                         (Prims.mk_range
                                                            "FStar.InteractiveHelpers.Effectful.fst"
                                                            (Prims.of_int (70))
                                                            (Prims.of_int (2))
                                                            (Prims.of_int (70))
                                                            (Prims.of_int (26)))
                                                         (Prims.mk_range
                                                            "prims.fst"
                                                            (Prims.of_int (606))
                                                            (Prims.of_int (19))
                                                            (Prims.of_int (606))
                                                            (Prims.of_int (31)))
                                                         (Obj.magic
                                                            (FStar_Tactics_Builtins.term_to_string
                                                               info.head))
                                                         (fun uu___1 ->
                                                            FStar_Tactics_Effect.lift_div_tac
                                                              (fun uu___2 ->
                                                                 Prims.strcat
                                                                   uu___1
                                                                   (Prims.strcat
                                                                    ")\n["
                                                                    (Prims.strcat
                                                                    params_str
                                                                    "]"))))))
                                                   (fun uu___1 ->
                                                      FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___2 ->
                                                           Prims.strcat ") ("
                                                             uu___1))))
                                             (fun uu___1 ->
                                                FStar_Tactics_Effect.lift_div_tac
                                                  (fun uu___2 ->
                                                     Prims.strcat uu___
                                                       uu___1)))) uu___)))
                            (fun uu___ ->
                               FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___1 ->
                                    Prims.strcat "Mketerm_info (" uu___))))
                      uu___))) uu___)
let (mk_eterm_info :
  effect_info ->
    FStar_Reflection_Types.term -> cast_info Prims.list -> eterm_info)
  =
  fun uu___ ->
    fun uu___1 ->
      fun uu___2 -> { einfo = uu___; head = uu___1; parameters = uu___2 }
let rec (decompose_application_aux :
  FStar_Reflection_Types.env ->
    FStar_Reflection_Types.term ->
      ((FStar_Reflection_Types.term * cast_info Prims.list), unit)
        FStar_Tactics_Effect.tac_repr)
  =
  fun e ->
    fun t ->
      FStar_Tactics_Effect.tac_bind
        (Prims.mk_range "FStar.InteractiveHelpers.Effectful.fst"
           (Prims.of_int (83)) (Prims.of_int (8)) (Prims.of_int (83))
           (Prims.of_int (17)))
        (Prims.mk_range "FStar.InteractiveHelpers.Effectful.fst"
           (Prims.of_int (83)) (Prims.of_int (2)) (Prims.of_int (104))
           (Prims.of_int (14)))
        (Obj.magic (FStar_Tactics_Builtins.inspect t))
        (fun uu___ ->
           (fun uu___ ->
              match uu___ with
              | FStar_Reflection_Data.Tv_App (hd, (a, qualif)) ->
                  Obj.magic
                    (Obj.repr
                       (FStar_Tactics_Effect.tac_bind
                          (Prims.mk_range
                             "FStar.InteractiveHelpers.Effectful.fst"
                             (Prims.of_int (85)) (Prims.of_int (22))
                             (Prims.of_int (85)) (Prims.of_int (52)))
                          (Prims.mk_range
                             "FStar.InteractiveHelpers.Effectful.fst"
                             (Prims.of_int (85)) (Prims.of_int (4))
                             (Prims.of_int (103)) (Prims.of_int (28)))
                          (Obj.magic (decompose_application_aux e hd))
                          (fun uu___1 ->
                             (fun uu___1 ->
                                match uu___1 with
                                | (hd0, params) ->
                                    Obj.magic
                                      (FStar_Tactics_Effect.tac_bind
                                         (Prims.mk_range
                                            "FStar.InteractiveHelpers.Effectful.fst"
                                            (Prims.of_int (87))
                                            (Prims.of_int (17))
                                            (Prims.of_int (87))
                                            (Prims.of_int (34)))
                                         (Prims.mk_range
                                            "FStar.InteractiveHelpers.Effectful.fst"
                                            (Prims.of_int (89))
                                            (Prims.of_int (4))
                                            (Prims.of_int (103))
                                            (Prims.of_int (28)))
                                         (Obj.magic
                                            (FStar_InteractiveHelpers_ExploreTerm.get_type_info
                                               e a))
                                         (fun uu___2 ->
                                            (fun a_type ->
                                               Obj.magic
                                                 (FStar_Tactics_Effect.tac_bind
                                                    (Prims.mk_range
                                                       "FStar.InteractiveHelpers.Effectful.fst"
                                                       (Prims.of_int (89))
                                                       (Prims.of_int (16))
                                                       (Prims.of_int (89))
                                                       (Prims.of_int (28)))
                                                    (Prims.mk_range
                                                       "FStar.InteractiveHelpers.Effectful.fst"
                                                       (Prims.of_int (90))
                                                       (Prims.of_int (4))
                                                       (Prims.of_int (103))
                                                       (Prims.of_int (28)))
                                                    (Obj.magic
                                                       (FStar_InteractiveHelpers_ExploreTerm.safe_tc
                                                          e hd))
                                                    (fun uu___2 ->
                                                       (fun hd_ty ->
                                                          Obj.magic
                                                            (FStar_Tactics_Effect.tac_bind
                                                               (Prims.mk_range
                                                                  "FStar.InteractiveHelpers.Effectful.fst"
                                                                  (Prims.of_int (91))
                                                                  (Prims.of_int (6))
                                                                  (Prims.of_int (100))
                                                                  (Prims.of_int (19)))
                                                               (Prims.mk_range
                                                                  "FStar.InteractiveHelpers.Effectful.fst"
                                                                  (Prims.of_int (103))
                                                                  (Prims.of_int (4))
                                                                  (Prims.of_int (103))
                                                                  (Prims.of_int (28)))
                                                               (match hd_ty
                                                                with
                                                                | FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Pervasives_Native.None)))
                                                                | FStar_Pervasives_Native.Some
                                                                    hd_ty' ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (28)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (100))
                                                                    (Prims.of_int (19)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Builtins.inspect
                                                                    hd_ty'))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    match uu___2
                                                                    with
                                                                    | 
                                                                    FStar_Reflection_Data.Tv_Arrow
                                                                    (b, c) ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (47)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (99))
                                                                    (Prims.of_int (43)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    (FStar_Reflection_Builtins.inspect_binder
                                                                    b).FStar_Reflection_Data.binder_bv))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun bv
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (35)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (98))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (99))
                                                                    (Prims.of_int (43)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Reflection_Builtins.inspect_bv
                                                                    bv))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    bview ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (98))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (98))
                                                                    (Prims.of_int (32)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (99))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (99))
                                                                    (Prims.of_int (43)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    bview.FStar_Reflection_Data.bv_sort))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun ty
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (99))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (99))
                                                                    (Prims.of_int (43)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (99))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (99))
                                                                    (Prims.of_int (43)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_ExploreTerm.get_type_info_from_type
                                                                    ty))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___3))))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    | 
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Pervasives_Native.None))))
                                                                    uu___2))))
                                                               (fun
                                                                  param_type
                                                                  ->
                                                                  FStar_Tactics_Effect.lift_div_tac
                                                                    (
                                                                    fun
                                                                    uu___2 ->
                                                                    (hd0,
                                                                    ((mk_cast_info
                                                                    a a_type
                                                                    param_type)
                                                                    ::
                                                                    params))))))
                                                         uu___2))) uu___2)))
                               uu___1)))
              | uu___1 ->
                  Obj.magic
                    (Obj.repr
                       (FStar_Tactics_Effect.lift_div_tac
                          (fun uu___2 -> (t, []))))) uu___)
let (decompose_application :
  FStar_Reflection_Types.env ->
    FStar_Reflection_Types.term ->
      ((FStar_Reflection_Types.term * cast_info Prims.list), unit)
        FStar_Tactics_Effect.tac_repr)
  =
  fun e ->
    fun t ->
      FStar_Tactics_Effect.tac_bind
        (Prims.mk_range "FStar.InteractiveHelpers.Effectful.fst"
           (Prims.of_int (108)) (Prims.of_int (19)) (Prims.of_int (108))
           (Prims.of_int (48)))
        (Prims.mk_range "FStar.InteractiveHelpers.Effectful.fst"
           (Prims.of_int (108)) (Prims.of_int (2)) (Prims.of_int (109))
           (Prims.of_int (25))) (Obj.magic (decompose_application_aux e t))
        (fun uu___ ->
           FStar_Tactics_Effect.lift_div_tac
             (fun uu___1 ->
                match uu___ with
                | (hd, params) -> (hd, (FStar_List_Tot_Base.rev params))))
let (comp_view_to_effect_info :
  Prims.bool ->
    FStar_Reflection_Data.comp_view ->
      (effect_info FStar_Pervasives_Native.option, unit)
        FStar_Tactics_Effect.tac_repr)
  =
  fun dbg ->
    fun cv ->
      match cv with
      | FStar_Reflection_Data.C_Total ret_ty ->
          FStar_Tactics_Effect.tac_bind
            (Prims.mk_range "FStar.InteractiveHelpers.Effectful.fst"
               (Prims.of_int (117)) (Prims.of_int (24)) (Prims.of_int (117))
               (Prims.of_int (54)))
            (Prims.mk_range "FStar.InteractiveHelpers.Effectful.fst"
               (Prims.of_int (118)) (Prims.of_int (4)) (Prims.of_int (118))
               (Prims.of_int (57)))
            (Obj.magic
               (FStar_InteractiveHelpers_ExploreTerm.get_type_info_from_type
                  ret_ty))
            (fun ret_type_info ->
               FStar_Tactics_Effect.lift_div_tac
                 (fun uu___ ->
                    FStar_Pervasives_Native.Some
                      (mk_effect_info
                         FStar_InteractiveHelpers_ExploreTerm.E_Total
                         ret_type_info FStar_Pervasives_Native.None
                         FStar_Pervasives_Native.None)))
      | FStar_Reflection_Data.C_GTotal ret_ty ->
          FStar_Tactics_Effect.tac_bind
            (Prims.mk_range "FStar.InteractiveHelpers.Effectful.fst"
               (Prims.of_int (120)) (Prims.of_int (24)) (Prims.of_int (120))
               (Prims.of_int (54)))
            (Prims.mk_range "FStar.InteractiveHelpers.Effectful.fst"
               (Prims.of_int (121)) (Prims.of_int (4)) (Prims.of_int (121))
               (Prims.of_int (57)))
            (Obj.magic
               (FStar_InteractiveHelpers_ExploreTerm.get_type_info_from_type
                  ret_ty))
            (fun ret_type_info ->
               FStar_Tactics_Effect.lift_div_tac
                 (fun uu___ ->
                    FStar_Pervasives_Native.Some
                      (mk_effect_info
                         FStar_InteractiveHelpers_ExploreTerm.E_Total
                         ret_type_info FStar_Pervasives_Native.None
                         FStar_Pervasives_Native.None)))
      | FStar_Reflection_Data.C_Lemma (pre, post, patterns) ->
          FStar_Tactics_Effect.tac_bind
            (Prims.mk_range "FStar.InteractiveHelpers.Effectful.fst"
               (Prims.of_int (124)) (Prims.of_int (14)) (Prims.of_int (124))
               (Prims.of_int (35)))
            (Prims.mk_range "FStar.InteractiveHelpers.Effectful.fst"
               (Prims.of_int (125)) (Prims.of_int (4)) (Prims.of_int (126))
               (Prims.of_int (71)))
            (Obj.magic (FStar_InteractiveHelpers_Base.prettify_term dbg pre))
            (fun uu___ ->
               (fun pre1 ->
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (Prims.mk_range
                          "FStar.InteractiveHelpers.Effectful.fst"
                          (Prims.of_int (125)) (Prims.of_int (15))
                          (Prims.of_int (125)) (Prims.of_int (37)))
                       (Prims.mk_range
                          "FStar.InteractiveHelpers.Effectful.fst"
                          (Prims.of_int (126)) (Prims.of_int (4))
                          (Prims.of_int (126)) (Prims.of_int (71)))
                       (Obj.magic
                          (FStar_InteractiveHelpers_Base.prettify_term dbg
                             post))
                       (fun post1 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___ ->
                               FStar_Pervasives_Native.Some
                                 (mk_effect_info
                                    FStar_InteractiveHelpers_ExploreTerm.E_Lemma
                                    FStar_InteractiveHelpers_ExploreTerm.unit_type_info
                                    (FStar_Pervasives_Native.Some pre1)
                                    (FStar_Pervasives_Native.Some post1))))))
                 uu___)
      | FStar_Reflection_Data.C_Eff
          (univs, eff_name, ret_ty, eff_args, uu___) ->
          FStar_Tactics_Effect.tac_bind
            (Prims.mk_range "FStar.InteractiveHelpers.Effectful.fst"
               (Prims.of_int (128)) (Prims.of_int (4)) (Prims.of_int (128))
               (Prims.of_int (78)))
            (Prims.mk_range "FStar.InteractiveHelpers.Effectful.fst"
               (Prims.of_int (129)) (Prims.of_int (4)) (Prims.of_int (145))
               (Prims.of_int (7)))
            (Obj.magic
               (FStar_InteractiveHelpers_Base.print_dbg dbg
                  (Prims.strcat "comp_view_to_effect_info: C_Eff "
                     (FStar_Reflection_Derived.flatten_name eff_name))))
            (fun uu___1 ->
               (fun uu___1 ->
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (Prims.mk_range
                          "FStar.InteractiveHelpers.Effectful.fst"
                          (Prims.of_int (129)) (Prims.of_int (24))
                          (Prims.of_int (129)) (Prims.of_int (54)))
                       (Prims.mk_range
                          "FStar.InteractiveHelpers.Effectful.fst"
                          (Prims.of_int (130)) (Prims.of_int (4))
                          (Prims.of_int (145)) (Prims.of_int (7)))
                       (Obj.magic
                          (FStar_InteractiveHelpers_ExploreTerm.get_type_info_from_type
                             ret_ty))
                       (fun uu___2 ->
                          (fun ret_type_info ->
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (Prims.mk_range
                                     "FStar.InteractiveHelpers.Effectful.fst"
                                     (Prims.of_int (130)) (Prims.of_int (16))
                                     (Prims.of_int (130)) (Prims.of_int (44)))
                                  (Prims.mk_range
                                     "FStar.InteractiveHelpers.Effectful.fst"
                                     (Prims.of_int (131)) (Prims.of_int (4))
                                     (Prims.of_int (145)) (Prims.of_int (7)))
                                  (FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___2 ->
                                        FStar_InteractiveHelpers_ExploreTerm.effect_name_to_type
                                          eff_name))
                                  (fun uu___2 ->
                                     (fun etype ->
                                        Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (Prims.mk_range
                                                "FStar.InteractiveHelpers.Effectful.fst"
                                                (Prims.of_int (131))
                                                (Prims.of_int (17))
                                                (Prims.of_int (131))
                                                (Prims.of_int (51)))
                                             (Prims.mk_range
                                                "FStar.InteractiveHelpers.Effectful.fst"
                                                (Prims.of_int (132))
                                                (Prims.of_int (4))
                                                (Prims.of_int (145))
                                                (Prims.of_int (7)))
                                             (FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___2 ->
                                                   mk_effect_info etype
                                                     ret_type_info))
                                             (fun uu___2 ->
                                                (fun mk_res ->
                                                   Obj.magic
                                                     (FStar_Tactics_Effect.tac_bind
                                                        (Prims.mk_range
                                                           "FStar.InteractiveHelpers.Effectful.fst"
                                                           (Prims.of_int (132))
                                                           (Prims.of_int (19))
                                                           (Prims.of_int (132))
                                                           (Prims.of_int (71)))
                                                        (Prims.mk_range
                                                           "FStar.InteractiveHelpers.Effectful.fst"
                                                           (Prims.of_int (133))
                                                           (Prims.of_int (10))
                                                           (Prims.of_int (144))
                                                           (Prims.of_int (15)))
                                                        (Obj.magic
                                                           (FStar_Tactics_Util.map
                                                              (fun uu___2 ->
                                                                 match uu___2
                                                                 with
                                                                 | (x, a) ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (132))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (132))
                                                                    (Prims.of_int (57)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (132))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (132))
                                                                    (Prims.of_int (61)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.prettify_term
                                                                    dbg x))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    (uu___3,
                                                                    a))))
                                                              eff_args))
                                                        (fun eff_args1 ->
                                                           FStar_Tactics_Effect.lift_div_tac
                                                             (fun uu___2 ->
                                                                match 
                                                                  (etype,
                                                                    eff_args1)
                                                                with
                                                                | (FStar_InteractiveHelpers_ExploreTerm.E_PURE,
                                                                   (pre,
                                                                    uu___3)::[])
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    (mk_res
                                                                    (FStar_Pervasives_Native.Some
                                                                    pre)
                                                                    FStar_Pervasives_Native.None)
                                                                | (FStar_InteractiveHelpers_ExploreTerm.E_Pure,
                                                                   (pre,
                                                                    uu___3)::
                                                                   (post,
                                                                    uu___4)::[])
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    (mk_res
                                                                    (FStar_Pervasives_Native.Some
                                                                    pre)
                                                                    (FStar_Pervasives_Native.Some
                                                                    post))
                                                                | (FStar_InteractiveHelpers_ExploreTerm.E_Stack,
                                                                   (pre,
                                                                    uu___3)::
                                                                   (post,
                                                                    uu___4)::[])
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    (mk_res
                                                                    (FStar_Pervasives_Native.Some
                                                                    pre)
                                                                    (FStar_Pervasives_Native.Some
                                                                    post))
                                                                | (FStar_InteractiveHelpers_ExploreTerm.E_ST,
                                                                   (pre,
                                                                    uu___3)::
                                                                   (post,
                                                                    uu___4)::[])
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
                                                                    uu___3)::[])
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    (mk_res
                                                                    (FStar_Pervasives_Native.Some
                                                                    pre)
                                                                    FStar_Pervasives_Native.None)
                                                                | (FStar_InteractiveHelpers_ExploreTerm.E_Unknown,
                                                                   (pre,
                                                                    uu___3)::
                                                                   (post,
                                                                    uu___4)::[])
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    (mk_res
                                                                    (FStar_Pervasives_Native.Some
                                                                    pre)
                                                                    (FStar_Pervasives_Native.Some
                                                                    post))
                                                                | uu___3 ->
                                                                    FStar_Pervasives_Native.None))))
                                                  uu___2))) uu___2))) uu___2)))
                 uu___1)
let (comp_to_effect_info :
  Prims.bool ->
    FStar_Reflection_Types.comp ->
      (effect_info FStar_Pervasives_Native.option, unit)
        FStar_Tactics_Effect.tac_repr)
  =
  fun dbg ->
    fun c ->
      FStar_Tactics_Effect.tac_bind
        (Prims.mk_range "FStar.InteractiveHelpers.Effectful.fst"
           (Prims.of_int (150)) (Prims.of_int (23)) (Prims.of_int (150))
           (Prims.of_int (37)))
        (Prims.mk_range "FStar.InteractiveHelpers.Effectful.fst"
           (Prims.of_int (151)) (Prims.of_int (2)) (Prims.of_int (151))
           (Prims.of_int (33)))
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___ -> FStar_Reflection_Builtins.inspect_comp c))
        (fun uu___ ->
           (fun cv -> Obj.magic (comp_view_to_effect_info dbg cv)) uu___)
let (compute_effect_info :
  Prims.bool ->
    FStar_Reflection_Types.env ->
      FStar_Reflection_Types.term ->
        (effect_info FStar_Pervasives_Native.option, unit)
          FStar_Tactics_Effect.tac_repr)
  =
  fun dbg ->
    fun e ->
      fun tm ->
        FStar_Tactics_Effect.tac_bind
          (Prims.mk_range "FStar.InteractiveHelpers.Effectful.fst"
             (Prims.of_int (156)) (Prims.of_int (8)) (Prims.of_int (156))
             (Prims.of_int (21)))
          (Prims.mk_range "FStar.InteractiveHelpers.Effectful.fst"
             (Prims.of_int (156)) (Prims.of_int (2)) (Prims.of_int (158))
             (Prims.of_int (16)))
          (Obj.magic (FStar_InteractiveHelpers_ExploreTerm.safe_tcc e tm))
          (fun uu___ ->
             (fun uu___ ->
                match uu___ with
                | FStar_Pervasives_Native.Some c ->
                    Obj.magic (Obj.repr (comp_to_effect_info dbg c))
                | FStar_Pervasives_Native.None ->
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___1 -> FStar_Pervasives_Native.None))))
               uu___)
let (typ_or_comp_to_effect_info :
  Prims.bool ->
    FStar_InteractiveHelpers_Base.genv ->
      FStar_InteractiveHelpers_ExploreTerm.typ_or_comp ->
        (effect_info, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun dbg ->
    fun ge ->
      fun c ->
        FStar_Tactics_Effect.tac_bind
          (Prims.mk_range "FStar.InteractiveHelpers.Effectful.fst"
             (Prims.of_int (173)) (Prims.of_int (10)) (Prims.of_int (173))
             (Prims.of_int (40)))
          (Prims.mk_range "FStar.InteractiveHelpers.Effectful.fst"
             (Prims.of_int (174)) (Prims.of_int (2)) (Prims.of_int (182))
             (Prims.of_int (25)))
          (Obj.magic
             (FStar_InteractiveHelpers_ExploreTerm.flush_typ_or_comp dbg
                ge.FStar_InteractiveHelpers_Base.env c))
          (fun uu___ ->
             (fun c1 ->
                match c1 with
                | FStar_InteractiveHelpers_ExploreTerm.TC_Typ
                    (ty, uu___, uu___1) ->
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (Prims.mk_range
                            "FStar.InteractiveHelpers.Effectful.fst"
                            (Prims.of_int (176)) (Prims.of_int (16))
                            (Prims.of_int (176)) (Prims.of_int (42)))
                         (Prims.mk_range
                            "FStar.InteractiveHelpers.Effectful.fst"
                            (Prims.of_int (177)) (Prims.of_int (4))
                            (Prims.of_int (177)) (Prims.of_int (42)))
                         (Obj.magic
                            (FStar_InteractiveHelpers_ExploreTerm.get_type_info_from_type
                               ty))
                         (fun tinfo ->
                            FStar_Tactics_Effect.lift_div_tac
                              (fun uu___2 ->
                                 mk_effect_info
                                   FStar_InteractiveHelpers_ExploreTerm.E_Total
                                   tinfo FStar_Pervasives_Native.None
                                   FStar_Pervasives_Native.None)))
                | FStar_InteractiveHelpers_ExploreTerm.TC_Comp
                    (cv, uu___, uu___1) ->
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (Prims.mk_range
                            "FStar.InteractiveHelpers.Effectful.fst"
                            (Prims.of_int (179)) (Prims.of_int (20))
                            (Prims.of_int (179)) (Prims.of_int (46)))
                         (Prims.mk_range
                            "FStar.InteractiveHelpers.Effectful.fst"
                            (Prims.of_int (180)) (Prims.of_int (4))
                            (Prims.of_int (182)) (Prims.of_int (25)))
                         (Obj.magic (comp_to_effect_info dbg cv))
                         (fun uu___2 ->
                            (fun opt_einfo ->
                               match opt_einfo with
                               | FStar_Pervasives_Native.None ->
                                   Obj.magic
                                     (Obj.repr
                                        (FStar_Tactics_Effect.tac_bind
                                           (Prims.mk_range
                                              "FStar.InteractiveHelpers.Effectful.fst"
                                              (Prims.of_int (181))
                                              (Prims.of_int (20))
                                              (Prims.of_int (181))
                                              (Prims.of_int (83)))
                                           (Prims.mk_range
                                              "FStar.InteractiveHelpers.Effectful.fst"
                                              (Prims.of_int (181))
                                              (Prims.of_int (14))
                                              (Prims.of_int (181))
                                              (Prims.of_int (83)))
                                           (Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (Prims.mk_range
                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                    (Prims.of_int (181))
                                                    (Prims.of_int (64))
                                                    (Prims.of_int (181))
                                                    (Prims.of_int (82)))
                                                 (Prims.mk_range "prims.fst"
                                                    (Prims.of_int (606))
                                                    (Prims.of_int (19))
                                                    (Prims.of_int (606))
                                                    (Prims.of_int (31)))
                                                 (Obj.magic
                                                    (FStar_InteractiveHelpers_Base.acomp_to_string
                                                       cv))
                                                 (fun uu___2 ->
                                                    FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___3 ->
                                                         Prims.strcat
                                                           "typ_or_comp_to_effect_info failed on: "
                                                           uu___2))))
                                           (fun uu___2 ->
                                              (fun uu___2 ->
                                                 Obj.magic
                                                   (FStar_InteractiveHelpers_Base.mfail
                                                      uu___2)) uu___2)))
                               | FStar_Pervasives_Native.Some einfo ->
                                   Obj.magic
                                     (Obj.repr
                                        (FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___2 -> einfo)))) uu___2)))
               uu___)
let (tcc_no_lift :
  FStar_Reflection_Types.env ->
    FStar_Reflection_Types.term ->
      (FStar_Reflection_Types.comp, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun e ->
    fun t ->
      FStar_Tactics_Effect.tac_bind
        (Prims.mk_range "FStar.InteractiveHelpers.Effectful.fst"
           (Prims.of_int (195)) (Prims.of_int (8)) (Prims.of_int (195))
           (Prims.of_int (17)))
        (Prims.mk_range "FStar.InteractiveHelpers.Effectful.fst"
           (Prims.of_int (195)) (Prims.of_int (2)) (Prims.of_int (202))
           (Prims.of_int (11)))
        (Obj.magic (FStar_Tactics_Builtins.inspect t))
        (fun uu___ ->
           (fun uu___ ->
              match uu___ with
              | FStar_Reflection_Data.Tv_App (uu___1, uu___2) ->
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (Prims.mk_range
                          "FStar.InteractiveHelpers.Effectful.fst"
                          (Prims.of_int (197)) (Prims.of_int (19))
                          (Prims.of_int (197)) (Prims.of_int (32)))
                       (Prims.mk_range
                          "FStar.InteractiveHelpers.Effectful.fst"
                          (Prims.of_int (197)) (Prims.of_int (4))
                          (Prims.of_int (199)) (Prims.of_int (41)))
                       (Obj.magic (FStar_Tactics_Derived.collect_app t))
                       (fun uu___3 ->
                          (fun uu___3 ->
                             match uu___3 with
                             | (hd, args) ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (Prims.mk_range
                                         "FStar.InteractiveHelpers.Effectful.fst"
                                         (Prims.of_int (198))
                                         (Prims.of_int (12))
                                         (Prims.of_int (198))
                                         (Prims.of_int (20)))
                                      (Prims.mk_range
                                         "FStar.InteractiveHelpers.Effectful.fst"
                                         (Prims.of_int (199))
                                         (Prims.of_int (4))
                                         (Prims.of_int (199))
                                         (Prims.of_int (41)))
                                      (Obj.magic
                                         (FStar_Tactics_Builtins.tcc e hd))
                                      (fun uu___4 ->
                                         (fun c ->
                                            Obj.magic
                                              (FStar_InteractiveHelpers_ExploreTerm.inst_comp
                                                 e c
                                                 (FStar_List_Tot_Base.map
                                                    FStar_Pervasives_Native.fst
                                                    args))) uu___4))) uu___3))
              | uu___1 -> Obj.magic (FStar_Tactics_Builtins.tcc e t)) uu___)
let (compute_eterm_info :
  Prims.bool ->
    FStar_Reflection_Types.env ->
      FStar_Reflection_Types.term ->
        (eterm_info, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun dbg ->
    fun e ->
      fun t ->
        FStar_Tactics_Effect.tac_bind
          (Prims.mk_range "FStar.InteractiveHelpers.Effectful.fst"
             (Prims.of_int (210)) (Prims.of_int (23)) (Prims.of_int (210))
             (Prims.of_int (48)))
          (Prims.mk_range "FStar.InteractiveHelpers.Effectful.fst"
             (Prims.of_int (210)) (Prims.of_int (2)) (Prims.of_int (223))
             (Prims.of_int (16))) (Obj.magic (decompose_application e t))
          (fun uu___ ->
             (fun uu___ ->
                match uu___ with
                | (hd, parameters) ->
                    Obj.magic
                      (FStar_Tactics_Derived.try_with
                         (fun uu___1 ->
                            match () with
                            | () ->
                                FStar_Tactics_Effect.tac_bind
                                  (Prims.mk_range
                                     "FStar.InteractiveHelpers.Effectful.fst"
                                     (Prims.of_int (213)) (Prims.of_int (19))
                                     (Prims.of_int (213)) (Prims.of_int (34)))
                                  (Prims.mk_range
                                     "FStar.InteractiveHelpers.Effectful.fst"
                                     (Prims.of_int (214)) (Prims.of_int (4))
                                     (Prims.of_int (218)) (Prims.of_int (39)))
                                  (Obj.magic (tcc_no_lift e t))
                                  (fun uu___2 ->
                                     (fun c ->
                                        Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (Prims.mk_range
                                                "FStar.InteractiveHelpers.Effectful.fst"
                                                (Prims.of_int (214))
                                                (Prims.of_int (20))
                                                (Prims.of_int (214))
                                                (Prims.of_int (45)))
                                             (Prims.mk_range
                                                "FStar.InteractiveHelpers.Effectful.fst"
                                                (Prims.of_int (215))
                                                (Prims.of_int (4))
                                                (Prims.of_int (218))
                                                (Prims.of_int (39)))
                                             (Obj.magic
                                                (comp_to_effect_info dbg c))
                                             (fun uu___2 ->
                                                (fun opt_einfo ->
                                                   match opt_einfo with
                                                   | FStar_Pervasives_Native.None
                                                       ->
                                                       Obj.magic
                                                         (Obj.repr
                                                            (FStar_Tactics_Effect.tac_bind
                                                               (Prims.mk_range
                                                                  "FStar.InteractiveHelpers.Effectful.fst"
                                                                  (Prims.of_int (216))
                                                                  (Prims.of_int (20))
                                                                  (Prims.of_int (216))
                                                                  (Prims.of_int (74)))
                                                               (Prims.mk_range
                                                                  "FStar.InteractiveHelpers.Effectful.fst"
                                                                  (Prims.of_int (216))
                                                                  (Prims.of_int (14))
                                                                  (Prims.of_int (216))
                                                                  (Prims.of_int (74)))
                                                               (Obj.magic
                                                                  (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (216))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (216))
                                                                    (Prims.of_int (73)))
                                                                    (Prims.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Builtins.term_to_string
                                                                    t))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Prims.strcat
                                                                    "compute_eterm_info: failed on: "
                                                                    uu___2))))
                                                               (fun uu___2 ->
                                                                  (fun uu___2
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.mfail
                                                                    uu___2))
                                                                    uu___2)))
                                                   | FStar_Pervasives_Native.Some
                                                       einfo ->
                                                       Obj.magic
                                                         (Obj.repr
                                                            (FStar_Tactics_Effect.lift_div_tac
                                                               (fun uu___2 ->
                                                                  mk_eterm_info
                                                                    einfo hd
                                                                    parameters))))
                                                  uu___2))) uu___2))
                         (fun uu___1 ->
                            (fun uu___1 ->
                               match uu___1 with
                               | FStar_Tactics_Common.TacticFailure msg ->
                                   Obj.magic
                                     (Obj.repr
                                        (FStar_InteractiveHelpers_Base.mfail
                                           (Prims.strcat
                                              "compute_eterm_info: failure: '"
                                              (Prims.strcat msg "'"))))
                               | e1 ->
                                   Obj.magic
                                     (Obj.repr
                                        (FStar_Tactics_Effect.raise e1)))
                              uu___1))) uu___)
let (has_refinement :
  FStar_InteractiveHelpers_ExploreTerm.type_info -> Prims.bool) =
  fun ty ->
    FStar_Pervasives_Native.uu___is_Some
      ty.FStar_InteractiveHelpers_ExploreTerm.refin
let (get_refinement :
  FStar_InteractiveHelpers_ExploreTerm.type_info ->
    FStar_Reflection_Types.term)
  =
  fun ty ->
    FStar_Pervasives_Native.__proj__Some__item__v
      ty.FStar_InteractiveHelpers_ExploreTerm.refin
let (get_opt_refinment :
  FStar_InteractiveHelpers_ExploreTerm.type_info ->
    FStar_Reflection_Types.term FStar_Pervasives_Native.option)
  = fun ty -> ty.FStar_InteractiveHelpers_ExploreTerm.refin
let (get_rawest_type :
  FStar_InteractiveHelpers_ExploreTerm.type_info ->
    FStar_Reflection_Types.typ)
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
        FStar_Tactics_Effect.tac_bind
          (Prims.mk_range "FStar.InteractiveHelpers.Effectful.fst"
             (Prims.of_int (255)) (Prims.of_int (2)) (Prims.of_int (255))
             (Prims.of_int (34)))
          (Prims.mk_range "FStar.InteractiveHelpers.Effectful.fst"
             (Prims.of_int (256)) (Prims.of_int (2)) (Prims.of_int (279))
             (Prims.of_int (13)))
          (Obj.magic
             (FStar_InteractiveHelpers_Base.print_dbg dbg "[> compare_types"))
          (fun uu___ ->
             (fun uu___ ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (Prims.mk_range "FStar.InteractiveHelpers.Effectful.fst"
                        (Prims.of_int (256)) (Prims.of_int (5))
                        (Prims.of_int (256)) (Prims.of_int (30)))
                     (Prims.mk_range "FStar.InteractiveHelpers.Effectful.fst"
                        (Prims.of_int (256)) (Prims.of_int (2))
                        (Prims.of_int (279)) (Prims.of_int (13)))
                     (Obj.magic
                        (term_eq
                           info1.FStar_InteractiveHelpers_ExploreTerm.ty
                           info2.FStar_InteractiveHelpers_ExploreTerm.ty))
                     (fun uu___1 ->
                        (fun uu___1 ->
                           if uu___1
                           then
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (Prims.mk_range
                                     "FStar.InteractiveHelpers.Effectful.fst"
                                     (Prims.of_int (257)) (Prims.of_int (14))
                                     (Prims.of_int (257)) (Prims.of_int (48)))
                                  (Prims.mk_range
                                     "FStar.InteractiveHelpers.Effectful.fst"
                                     (Prims.of_int (258)) (Prims.of_int (6))
                                     (Prims.of_int (276)) (Prims.of_int (15)))
                                  (Obj.magic
                                     (FStar_InteractiveHelpers_Base.print_dbg
                                        dbg "-> types are equal"))
                                  (fun uu___2 ->
                                     (fun uu___2 ->
                                        if has_refinement info2
                                        then
                                          Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (Prims.mk_range
                                                  "FStar.InteractiveHelpers.Effectful.fst"
                                                  (Prims.of_int (259))
                                                  (Prims.of_int (16))
                                                  (Prims.of_int (259))
                                                  (Prims.of_int (58)))
                                               (Prims.mk_range
                                                  "FStar.InteractiveHelpers.Effectful.fst"
                                                  (Prims.of_int (262))
                                                  (Prims.of_int (8))
                                                  (Prims.of_int (273))
                                                  (Prims.of_int (23)))
                                               (Obj.magic
                                                  (FStar_InteractiveHelpers_Base.print_dbg
                                                     dbg
                                                     "-> 2nd type has refinement"))
                                               (fun uu___3 ->
                                                  (fun uu___3 ->
                                                     if has_refinement info1
                                                     then
                                                       Obj.magic
                                                         (FStar_Tactics_Effect.tac_bind
                                                            (Prims.mk_range
                                                               "FStar.InteractiveHelpers.Effectful.fst"
                                                               (Prims.of_int (263))
                                                               (Prims.of_int (18))
                                                               (Prims.of_int (263))
                                                               (Prims.of_int (60)))
                                                            (Prims.mk_range
                                                               "FStar.InteractiveHelpers.Effectful.fst"
                                                               (Prims.of_int (264))
                                                               (Prims.of_int (10))
                                                               (Prims.of_int (269))
                                                               (Prims.of_int (23)))
                                                            (Obj.magic
                                                               (FStar_InteractiveHelpers_Base.print_dbg
                                                                  dbg
                                                                  "-> 1st type has refinement"))
                                                            (fun uu___4 ->
                                                               (fun uu___4 ->
                                                                  Obj.magic
                                                                    (
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (264))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (264))
                                                                    (Prims.of_int (66)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (264))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (269))
                                                                    (Prims.of_int (23)))
                                                                    (Obj.magic
                                                                    (term_eq
                                                                    (get_refinement
                                                                    info1)
                                                                    (get_refinement
                                                                    info2)))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    if uu___5
                                                                    then
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (265))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (265))
                                                                    (Prims.of_int (46)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (266))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (266))
                                                                    (Prims.of_int (19)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    "-> Refines"))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    Refines)))
                                                                    else
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (268))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (268))
                                                                    (Prims.of_int (50)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (269))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (269))
                                                                    (Prims.of_int (23)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    "-> Same_raw_type"))
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    Same_raw_type))))
                                                                    uu___5)))
                                                                 uu___4))
                                                     else
                                                       Obj.magic
                                                         (FStar_Tactics_Effect.tac_bind
                                                            (Prims.mk_range
                                                               "FStar.InteractiveHelpers.Effectful.fst"
                                                               (Prims.of_int (271))
                                                               (Prims.of_int (18))
                                                               (Prims.of_int (271))
                                                               (Prims.of_int (63)))
                                                            (Prims.mk_range
                                                               "FStar.InteractiveHelpers.Effectful.fst"
                                                               (Prims.of_int (272))
                                                               (Prims.of_int (10))
                                                               (Prims.of_int (273))
                                                               (Prims.of_int (23)))
                                                            (Obj.magic
                                                               (FStar_InteractiveHelpers_Base.print_dbg
                                                                  dbg
                                                                  "-> 1st type has no refinement"))
                                                            (fun uu___5 ->
                                                               (fun uu___5 ->
                                                                  Obj.magic
                                                                    (
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (272))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (272))
                                                                    (Prims.of_int (50)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (273))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (273))
                                                                    (Prims.of_int (23)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    "-> Same_raw_type"))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    Same_raw_type))))
                                                                 uu___5)))
                                                    uu___3))
                                        else
                                          Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (Prims.mk_range
                                                  "FStar.InteractiveHelpers.Effectful.fst"
                                                  (Prims.of_int (275))
                                                  (Prims.of_int (16))
                                                  (Prims.of_int (275))
                                                  (Prims.of_int (70)))
                                               (Prims.mk_range
                                                  "FStar.InteractiveHelpers.Effectful.fst"
                                                  (Prims.of_int (276))
                                                  (Prims.of_int (8))
                                                  (Prims.of_int (276))
                                                  (Prims.of_int (15)))
                                               (Obj.magic
                                                  (FStar_InteractiveHelpers_Base.print_dbg
                                                     dbg
                                                     "-> 2nd type has no refinement: Refines"))
                                               (fun uu___4 ->
                                                  FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___5 -> Refines))))
                                       uu___2))
                           else
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (Prims.mk_range
                                     "FStar.InteractiveHelpers.Effectful.fst"
                                     (Prims.of_int (278)) (Prims.of_int (14))
                                     (Prims.of_int (278)) (Prims.of_int (49)))
                                  (Prims.mk_range
                                     "FStar.InteractiveHelpers.Effectful.fst"
                                     (Prims.of_int (279)) (Prims.of_int (6))
                                     (Prims.of_int (279)) (Prims.of_int (13)))
                                  (Obj.magic
                                     (FStar_InteractiveHelpers_Base.print_dbg
                                        dbg "types are not equal"))
                                  (fun uu___3 ->
                                     FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___4 -> Unknown)))) uu___1)))
               uu___)
let (compare_cast_types :
  Prims.bool ->
    cast_info -> (type_comparison, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun dbg ->
    fun p ->
      FStar_Tactics_Effect.tac_bind
        (Prims.mk_range "FStar.InteractiveHelpers.Effectful.fst"
           (Prims.of_int (285)) (Prims.of_int (2)) (Prims.of_int (285))
           (Prims.of_int (39)))
        (Prims.mk_range "FStar.InteractiveHelpers.Effectful.fst"
           (Prims.of_int (286)) (Prims.of_int (2)) (Prims.of_int (289))
           (Prims.of_int (16)))
        (Obj.magic
           (FStar_InteractiveHelpers_Base.print_dbg dbg
              "[> compare_cast_types"))
        (fun uu___ ->
           (fun uu___ ->
              match ((p.p_ty), (p.exp_ty)) with
              | (FStar_Pervasives_Native.Some info1,
                 FStar_Pervasives_Native.Some info2) ->
                  Obj.magic (Obj.repr (compare_types dbg info1 info2))
              | uu___1 ->
                  Obj.magic
                    (Obj.repr
                       (FStar_Tactics_Effect.lift_div_tac
                          (fun uu___2 -> Unknown)))) uu___)
let (mk_has_type :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.typ ->
      (FStar_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun t ->
         fun ty ->
           Obj.magic
             (FStar_Tactics_Effect.lift_div_tac
                (fun uu___ ->
                   FStar_Reflection_Derived.mk_app
                     (FStar_Reflection_Builtins.pack_ln
                        (FStar_Reflection_Data.Tv_FVar
                           (FStar_Reflection_Builtins.pack_fv
                              ["Prims"; "has_type"])))
                     [(ty, FStar_Reflection_Data.Q_Implicit);
                     (t, FStar_Reflection_Data.Q_Explicit);
                     (ty, FStar_Reflection_Data.Q_Explicit)]))) uu___1 uu___
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
        FStar_Tactics_Effect.tac_bind
          (Prims.mk_range "FStar.InteractiveHelpers.Effectful.fst"
             (Prims.of_int (316)) (Prims.of_int (2)) (Prims.of_int (316))
             (Prims.of_int (76)))
          (Prims.mk_range "FStar.InteractiveHelpers.Effectful.fst"
             (Prims.of_int (317)) (Prims.of_int (2)) (Prims.of_int (344))
             (Prims.of_int (13)))
          (Obj.magic
             (FStar_Tactics_Effect.tac_bind
                (Prims.mk_range "FStar.InteractiveHelpers.Effectful.fst"
                   (Prims.of_int (316)) (Prims.of_int (16))
                   (Prims.of_int (316)) (Prims.of_int (76)))
                (Prims.mk_range "FStar.InteractiveHelpers.Effectful.fst"
                   (Prims.of_int (316)) (Prims.of_int (2))
                   (Prims.of_int (316)) (Prims.of_int (76)))
                (Obj.magic
                   (FStar_Tactics_Effect.tac_bind
                      (Prims.mk_range
                         "FStar.InteractiveHelpers.Effectful.fst"
                         (Prims.of_int (316)) (Prims.of_int (53))
                         (Prims.of_int (316)) (Prims.of_int (75)))
                      (Prims.mk_range "prims.fst" (Prims.of_int (606))
                         (Prims.of_int (19)) (Prims.of_int (606))
                         (Prims.of_int (31)))
                      (Obj.magic (cast_info_to_string ci))
                      (fun uu___ ->
                         FStar_Tactics_Effect.lift_div_tac
                           (fun uu___1 ->
                              Prims.strcat "[> cast_info_to_propositions:\n"
                                uu___))))
                (fun uu___ ->
                   (fun uu___ ->
                      Obj.magic
                        (FStar_InteractiveHelpers_Base.print_dbg dbg uu___))
                     uu___)))
          (fun uu___ ->
             (fun uu___ ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (Prims.mk_range "FStar.InteractiveHelpers.Effectful.fst"
                        (Prims.of_int (317)) (Prims.of_int (8))
                        (Prims.of_int (317)) (Prims.of_int (33)))
                     (Prims.mk_range "FStar.InteractiveHelpers.Effectful.fst"
                        (Prims.of_int (317)) (Prims.of_int (2))
                        (Prims.of_int (344)) (Prims.of_int (13)))
                     (Obj.magic (compare_cast_types dbg ci))
                     (fun uu___1 ->
                        (fun uu___1 ->
                           match uu___1 with
                           | Refines ->
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (Prims.mk_range
                                       "FStar.InteractiveHelpers.Effectful.fst"
                                       (Prims.of_int (319))
                                       (Prims.of_int (4))
                                       (Prims.of_int (319))
                                       (Prims.of_int (51)))
                                    (Prims.mk_range
                                       "FStar.InteractiveHelpers.Effectful.fst"
                                       (Prims.of_int (320))
                                       (Prims.of_int (4))
                                       (Prims.of_int (320))
                                       (Prims.of_int (6)))
                                    (Obj.magic
                                       (FStar_InteractiveHelpers_Base.print_dbg
                                          dbg "-> Comparison result: Refines"))
                                    (fun uu___2 ->
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___3 -> [])))
                           | Same_raw_type ->
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (Prims.mk_range
                                       "FStar.InteractiveHelpers.Effectful.fst"
                                       (Prims.of_int (322))
                                       (Prims.of_int (4))
                                       (Prims.of_int (322))
                                       (Prims.of_int (57)))
                                    (Prims.mk_range
                                       "FStar.InteractiveHelpers.Effectful.fst"
                                       (Prims.of_int (323))
                                       (Prims.of_int (4))
                                       (Prims.of_int (325))
                                       (Prims.of_int (16)))
                                    (Obj.magic
                                       (FStar_InteractiveHelpers_Base.print_dbg
                                          dbg
                                          "-> Comparison result: Same_raw_type"))
                                    (fun uu___2 ->
                                       (fun uu___2 ->
                                          Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (Prims.mk_range
                                                  "FStar.InteractiveHelpers.Effectful.fst"
                                                  (Prims.of_int (323))
                                                  (Prims.of_int (16))
                                                  (Prims.of_int (323))
                                                  (Prims.of_int (50)))
                                               (Prims.mk_range
                                                  "FStar.InteractiveHelpers.Effectful.fst"
                                                  (Prims.of_int (324))
                                                  (Prims.of_int (4))
                                                  (Prims.of_int (325))
                                                  (Prims.of_int (16)))
                                               (FStar_Tactics_Effect.lift_div_tac
                                                  (fun uu___3 ->
                                                     get_refinement
                                                       (FStar_Pervasives_Native.__proj__Some__item__v
                                                          ci.exp_ty)))
                                               (fun uu___3 ->
                                                  (fun refin ->
                                                     Obj.magic
                                                       (FStar_Tactics_Effect.tac_bind
                                                          (Prims.mk_range
                                                             "FStar.InteractiveHelpers.Effectful.fst"
                                                             (Prims.of_int (324))
                                                             (Prims.of_int (21))
                                                             (Prims.of_int (324))
                                                             (Prims.of_int (55)))
                                                          (Prims.mk_range
                                                             "FStar.InteractiveHelpers.Effectful.fst"
                                                             (Prims.of_int (325))
                                                             (Prims.of_int (4))
                                                             (Prims.of_int (325))
                                                             (Prims.of_int (16)))
                                                          (Obj.magic
                                                             (FStar_InteractiveHelpers_Base.mk_app_norm
                                                                ge.FStar_InteractiveHelpers_Base.env
                                                                refin
                                                                [ci.term]))
                                                          (fun inst_refin ->
                                                             FStar_Tactics_Effect.lift_div_tac
                                                               (fun uu___3 ->
                                                                  [inst_refin]))))
                                                    uu___3))) uu___2))
                           | Unknown ->
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (Prims.mk_range
                                       "FStar.InteractiveHelpers.Effectful.fst"
                                       (Prims.of_int (327))
                                       (Prims.of_int (4))
                                       (Prims.of_int (327))
                                       (Prims.of_int (51)))
                                    (Prims.mk_range
                                       "FStar.InteractiveHelpers.Effectful.fst"
                                       (Prims.of_int (328))
                                       (Prims.of_int (4))
                                       (Prims.of_int (344))
                                       (Prims.of_int (13)))
                                    (Obj.magic
                                       (FStar_InteractiveHelpers_Base.print_dbg
                                          dbg "-> Comparison result: Unknown"))
                                    (fun uu___2 ->
                                       (fun uu___2 ->
                                          match ((ci.p_ty), (ci.exp_ty)) with
                                          | (FStar_Pervasives_Native.Some
                                             p_ty,
                                             FStar_Pervasives_Native.Some
                                             e_ty) ->
                                              Obj.magic
                                                (Obj.repr
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (Prims.mk_range
                                                         "FStar.InteractiveHelpers.Effectful.fst"
                                                         (Prims.of_int (330))
                                                         (Prims.of_int (18))
                                                         (Prims.of_int (330))
                                                         (Prims.of_int (38)))
                                                      (Prims.mk_range
                                                         "FStar.InteractiveHelpers.Effectful.fst"
                                                         (Prims.of_int (331))
                                                         (Prims.of_int (6))
                                                         (Prims.of_int (343))
                                                         (Prims.of_int (41)))
                                                      (FStar_Tactics_Effect.lift_div_tac
                                                         (fun uu___3 ->
                                                            get_rawest_type
                                                              p_ty))
                                                      (fun uu___3 ->
                                                         (fun p_rty ->
                                                            Obj.magic
                                                              (FStar_Tactics_Effect.tac_bind
                                                                 (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (331))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (331))
                                                                    (Prims.of_int (38)))
                                                                 (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (338))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (343))
                                                                    (Prims.of_int (41)))
                                                                 (FStar_Tactics_Effect.lift_div_tac
                                                                    (
                                                                    fun
                                                                    uu___3 ->
                                                                    get_rawest_type
                                                                    e_ty))
                                                                 (fun uu___3
                                                                    ->
                                                                    (fun
                                                                    e_rty ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (338))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (338))
                                                                    (Prims.of_int (66)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (339))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (343))
                                                                    (Prims.of_int (41)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Builtins.pack
                                                                    (FStar_Reflection_Data.Tv_AscribedT
                                                                    ((ci.term),
                                                                    p_rty,
                                                                    FStar_Pervasives_Native.None,
                                                                    false))))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    ascr_term
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (339))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (339))
                                                                    (Prims.of_int (95)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (340))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (343))
                                                                    (Prims.of_int (41)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    [
                                                                    (p_rty,
                                                                    FStar_Reflection_Data.Q_Implicit);
                                                                    (ascr_term,
                                                                    FStar_Reflection_Data.Q_Explicit);
                                                                    (e_rty,
                                                                    FStar_Reflection_Data.Q_Explicit)]))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    has_type_params
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (340))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (340))
                                                                    (Prims.of_int (56)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (342))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (343))
                                                                    (Prims.of_int (41)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Reflection_Derived.mk_app
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["Prims";
                                                                    "has_type"])))
                                                                    has_type_params))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    type_cast
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (342))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (342))
                                                                    (Prims.of_int (70)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (343))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (343))
                                                                    (Prims.of_int (41)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.opt_mk_app_norm
                                                                    ge.FStar_InteractiveHelpers_Base.env
                                                                    e_ty.FStar_InteractiveHelpers_ExploreTerm.refin
                                                                    [ci.term]))
                                                                    (fun
                                                                    inst_opt_refin
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_InteractiveHelpers_Base.opt_cons
                                                                    inst_opt_refin
                                                                    [type_cast]))))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                           uu___3)))
                                          | uu___3 ->
                                              Obj.magic
                                                (Obj.repr
                                                   (FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___4 -> []))))
                                         uu___2))) uu___1))) uu___)
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
        FStar_Tactics_Effect.tac_bind
          (Prims.mk_range "FStar.InteractiveHelpers.Effectful.fst"
             (Prims.of_int (351)) (Prims.of_int (12)) (Prims.of_int (351))
             (Prims.of_int (53)))
          (Prims.mk_range "FStar.InteractiveHelpers.Effectful.fst"
             (Prims.of_int (352)) (Prims.of_int (2)) (Prims.of_int (352))
             (Prims.of_int (13)))
          (Obj.magic
             (FStar_Tactics_Util.map (cast_info_to_propositions dbg ge) ls))
          (fun lsl1 ->
             FStar_Tactics_Effect.lift_div_tac
               (fun uu___ -> FStar_List_Tot_Base.flatten lsl1))
type pre_post_type =
  | PP_Unknown 
  | PP_Pure 
  | PP_State of FStar_Reflection_Types.term 
let (uu___is_PP_Unknown : pre_post_type -> Prims.bool) =
  fun projectee -> match projectee with | PP_Unknown -> true | uu___ -> false
let (uu___is_PP_Pure : pre_post_type -> Prims.bool) =
  fun projectee -> match projectee with | PP_Pure -> true | uu___ -> false
let (uu___is_PP_State : pre_post_type -> Prims.bool) =
  fun projectee ->
    match projectee with | PP_State state_type -> true | uu___ -> false
let (__proj__PP_State__item__state_type :
  pre_post_type -> FStar_Reflection_Types.term) =
  fun projectee -> match projectee with | PP_State state_type -> state_type
let (compute_pre_type :
  Prims.bool ->
    FStar_Reflection_Types.env ->
      FStar_Reflection_Types.term ->
        (pre_post_type, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun dbg ->
    fun e ->
      fun pre ->
        FStar_Tactics_Effect.tac_bind
          (Prims.mk_range "FStar.InteractiveHelpers.Effectful.fst"
             (Prims.of_int (370)) (Prims.of_int (2)) (Prims.of_int (370))
             (Prims.of_int (37)))
          (Prims.mk_range "FStar.InteractiveHelpers.Effectful.fst"
             (Prims.of_int (371)) (Prims.of_int (2)) (Prims.of_int (388))
             (Prims.of_int (16)))
          (Obj.magic
             (FStar_InteractiveHelpers_Base.print_dbg dbg
                "[> compute_pre_type"))
          (fun uu___ ->
             (fun uu___ ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (Prims.mk_range "FStar.InteractiveHelpers.Effectful.fst"
                        (Prims.of_int (371)) (Prims.of_int (8))
                        (Prims.of_int (371)) (Prims.of_int (21)))
                     (Prims.mk_range "FStar.InteractiveHelpers.Effectful.fst"
                        (Prims.of_int (371)) (Prims.of_int (2))
                        (Prims.of_int (388)) (Prims.of_int (16)))
                     (Obj.magic
                        (FStar_InteractiveHelpers_ExploreTerm.safe_tc e pre))
                     (fun uu___1 ->
                        (fun uu___1 ->
                           match uu___1 with
                           | FStar_Pervasives_Native.None ->
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (Prims.mk_range
                                       "FStar.InteractiveHelpers.Effectful.fst"
                                       (Prims.of_int (373))
                                       (Prims.of_int (4))
                                       (Prims.of_int (373))
                                       (Prims.of_int (34)))
                                    (Prims.mk_range
                                       "FStar.InteractiveHelpers.Effectful.fst"
                                       (Prims.of_int (374))
                                       (Prims.of_int (4))
                                       (Prims.of_int (374))
                                       (Prims.of_int (14)))
                                    (Obj.magic
                                       (FStar_InteractiveHelpers_Base.print_dbg
                                          dbg "safe_tc failed"))
                                    (fun uu___2 ->
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___3 -> PP_Unknown)))
                           | FStar_Pervasives_Native.Some ty ->
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (Prims.mk_range
                                       "FStar.InteractiveHelpers.Effectful.fst"
                                       (Prims.of_int (376))
                                       (Prims.of_int (4))
                                       (Prims.of_int (376))
                                       (Prims.of_int (37)))
                                    (Prims.mk_range
                                       "FStar.InteractiveHelpers.Effectful.fst"
                                       (Prims.of_int (377))
                                       (Prims.of_int (4))
                                       (Prims.of_int (388))
                                       (Prims.of_int (16)))
                                    (Obj.magic
                                       (FStar_InteractiveHelpers_Base.print_dbg
                                          dbg "safe_tc succeeded"))
                                    (fun uu___2 ->
                                       (fun uu___2 ->
                                          Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (Prims.mk_range
                                                  "FStar.InteractiveHelpers.Effectful.fst"
                                                  (Prims.of_int (377))
                                                  (Prims.of_int (17))
                                                  (Prims.of_int (377))
                                                  (Prims.of_int (34)))
                                               (Prims.mk_range
                                                  "FStar.InteractiveHelpers.Effectful.fst"
                                                  (Prims.of_int (377))
                                                  (Prims.of_int (4))
                                                  (Prims.of_int (388))
                                                  (Prims.of_int (16)))
                                               (Obj.magic
                                                  (FStar_Tactics_SyntaxHelpers.collect_arr_bs
                                                     ty))
                                               (fun uu___3 ->
                                                  (fun uu___3 ->
                                                     match uu___3 with
                                                     | (brs, c) ->
                                                         Obj.magic
                                                           (FStar_Tactics_Effect.tac_bind
                                                              (Prims.mk_range
                                                                 "FStar.InteractiveHelpers.Effectful.fst"
                                                                 (Prims.of_int (378))
                                                                 (Prims.of_int (4))
                                                                 (Prims.of_int (378))
                                                                 (Prims.of_int (73)))
                                                              (Prims.mk_range
                                                                 "FStar.InteractiveHelpers.Effectful.fst"
                                                                 (Prims.of_int (379))
                                                                 (Prims.of_int (4))
                                                                 (Prims.of_int (388))
                                                                 (Prims.of_int (16)))
                                                              (Obj.magic
                                                                 (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    (
                                                                    Prims.strcat
                                                                    "num binders: "
                                                                    (Prims.string_of_int
                                                                    (FStar_List_Tot_Base.length
                                                                    brs)))))
                                                              (fun uu___4 ->
                                                                 (fun uu___4
                                                                    ->
                                                                    match 
                                                                    (brs,
                                                                    (FStar_InteractiveHelpers_ExploreTerm.is_total_or_gtotal
                                                                    c))
                                                                    with
                                                                    | 
                                                                    ([],
                                                                    true) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (381))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (381))
                                                                    (Prims.of_int (29)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (382))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (382))
                                                                    (Prims.of_int (13)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    "PP_Pure"))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    PP_Pure)))
                                                                    | 
                                                                    (b::[],
                                                                    true) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (384))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (384))
                                                                    (Prims.of_int (71)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (385))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (385))
                                                                    (Prims.of_int (33)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (384))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (384))
                                                                    (Prims.of_int (71)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (384))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (384))
                                                                    (Prims.of_int (71)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (384))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (384))
                                                                    (Prims.of_int (70)))
                                                                    (Prims.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Builtins.term_to_string
                                                                    (FStar_Reflection_Derived.type_of_binder
                                                                    b)))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Prims.strcat
                                                                    "PP_State "
                                                                    uu___5))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    uu___5))
                                                                    uu___5)))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    PP_State
                                                                    (FStar_Reflection_Derived.type_of_binder
                                                                    b))))
                                                                    | 
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (387))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (387))
                                                                    (Prims.of_int (32)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (388))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (388))
                                                                    (Prims.of_int (16)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    "PP_Unknown"))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    PP_Unknown))))
                                                                   uu___4)))
                                                    uu___3))) uu___2)))
                          uu___1))) uu___)
let (opt_remove_refin :
  FStar_Reflection_Types.typ ->
    (FStar_Reflection_Types.typ, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun ty ->
    FStar_Tactics_Effect.tac_bind
      (Prims.mk_range "FStar.InteractiveHelpers.Effectful.fst"
         (Prims.of_int (392)) (Prims.of_int (8)) (Prims.of_int (392))
         (Prims.of_int (18)))
      (Prims.mk_range "FStar.InteractiveHelpers.Effectful.fst"
         (Prims.of_int (392)) (Prims.of_int (2)) (Prims.of_int (394))
         (Prims.of_int (11))) (Obj.magic (FStar_Tactics_Builtins.inspect ty))
      (fun uu___ ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___1 ->
              match uu___ with
              | FStar_Reflection_Data.Tv_Refine (bv, uu___2) ->
                  (FStar_Reflection_Builtins.inspect_bv bv).FStar_Reflection_Data.bv_sort
              | uu___2 -> ty))
let (compute_post_type :
  Prims.bool ->
    FStar_Reflection_Types.env ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.term ->
          (pre_post_type, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun dbg ->
    fun e ->
      fun ret_type ->
        fun post ->
          FStar_Tactics_Effect.tac_bind
            (Prims.mk_range "FStar.InteractiveHelpers.Effectful.fst"
               (Prims.of_int (398)) (Prims.of_int (2)) (Prims.of_int (398))
               (Prims.of_int (38)))
            (Prims.mk_range "FStar.InteractiveHelpers.Effectful.fst"
               (Prims.of_int (399)) (Prims.of_int (2)) (Prims.of_int (446))
               (Prims.of_int (16)))
            (Obj.magic
               (FStar_InteractiveHelpers_Base.print_dbg dbg
                  "[> compute_post_type"))
            (fun uu___ ->
               (fun uu___ ->
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (Prims.mk_range
                          "FStar.InteractiveHelpers.Effectful.fst"
                          (Prims.of_int (400)) (Prims.of_int (4))
                          (Prims.of_int (402)) (Prims.of_int (18)))
                       (Prims.mk_range
                          "FStar.InteractiveHelpers.Effectful.fst"
                          (Prims.of_int (404)) (Prims.of_int (2))
                          (Prims.of_int (446)) (Prims.of_int (16)))
                       (FStar_Tactics_Effect.lift_div_tac
                          (fun uu___2 ->
                             fun uu___1 ->
                               (fun uu___1 ->
                                  fun c ->
                                    match FStar_InteractiveHelpers_ExploreTerm.get_total_or_gtotal_ret_type
                                            c
                                    with
                                    | FStar_Pervasives_Native.Some ret_ty ->
                                        Obj.magic
                                          (Obj.repr
                                             (FStar_Tactics_Effect.tac_bind
                                                (Prims.mk_range
                                                   "FStar.InteractiveHelpers.Effectful.fst"
                                                   (Prims.of_int (401))
                                                   (Prims.of_int (26))
                                                   (Prims.of_int (401))
                                                   (Prims.of_int (42)))
                                                (Prims.mk_range
                                                   "FStar.InteractiveHelpers.Effectful.fst"
                                                   (Prims.of_int (401))
                                                   (Prims.of_int (21))
                                                   (Prims.of_int (401))
                                                   (Prims.of_int (42)))
                                                (Obj.magic
                                                   (FStar_Tactics_Builtins.inspect
                                                      ret_ty))
                                                (fun uu___2 ->
                                                   FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___3 ->
                                                        FStar_Pervasives_Native.Some
                                                          uu___2))))
                                    | FStar_Pervasives_Native.None ->
                                        Obj.magic
                                          (Obj.repr
                                             (FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___2 ->
                                                   FStar_Pervasives_Native.None))))
                                 uu___2 uu___1))
                       (fun uu___1 ->
                          (fun get_tot_ret_type ->
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (Prims.mk_range
                                     "FStar.InteractiveHelpers.Effectful.fst"
                                     (Prims.of_int (404)) (Prims.of_int (8))
                                     (Prims.of_int (404)) (Prims.of_int (22)))
                                  (Prims.mk_range
                                     "FStar.InteractiveHelpers.Effectful.fst"
                                     (Prims.of_int (404)) (Prims.of_int (2))
                                     (Prims.of_int (446)) (Prims.of_int (16)))
                                  (Obj.magic
                                     (FStar_InteractiveHelpers_ExploreTerm.safe_tc
                                        e post))
                                  (fun uu___1 ->
                                     (fun uu___1 ->
                                        match uu___1 with
                                        | FStar_Pervasives_Native.None ->
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (Prims.mk_range
                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                    (Prims.of_int (406))
                                                    (Prims.of_int (4))
                                                    (Prims.of_int (406))
                                                    (Prims.of_int (34)))
                                                 (Prims.mk_range
                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                    (Prims.of_int (407))
                                                    (Prims.of_int (4))
                                                    (Prims.of_int (407))
                                                    (Prims.of_int (14)))
                                                 (Obj.magic
                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                       dbg "safe_tc failed"))
                                                 (fun uu___2 ->
                                                    FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___3 ->
                                                         PP_Unknown)))
                                        | FStar_Pervasives_Native.Some ty ->
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (Prims.mk_range
                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                    (Prims.of_int (409))
                                                    (Prims.of_int (4))
                                                    (Prims.of_int (409))
                                                    (Prims.of_int (37)))
                                                 (Prims.mk_range
                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                    (Prims.of_int (410))
                                                    (Prims.of_int (4))
                                                    (Prims.of_int (446))
                                                    (Prims.of_int (16)))
                                                 (Obj.magic
                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                       dbg
                                                       "safe_tc succeeded"))
                                                 (fun uu___2 ->
                                                    (fun uu___2 ->
                                                       Obj.magic
                                                         (FStar_Tactics_Effect.tac_bind
                                                            (Prims.mk_range
                                                               "FStar.InteractiveHelpers.Effectful.fst"
                                                               (Prims.of_int (410))
                                                               (Prims.of_int (17))
                                                               (Prims.of_int (410))
                                                               (Prims.of_int (34)))
                                                            (Prims.mk_range
                                                               "FStar.InteractiveHelpers.Effectful.fst"
                                                               (Prims.of_int (410))
                                                               (Prims.of_int (4))
                                                               (Prims.of_int (446))
                                                               (Prims.of_int (16)))
                                                            (Obj.magic
                                                               (FStar_Tactics_SyntaxHelpers.collect_arr_bs
                                                                  ty))
                                                            (fun uu___3 ->
                                                               (fun uu___3 ->
                                                                  match uu___3
                                                                  with
                                                                  | (brs, c)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (411))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (411))
                                                                    (Prims.of_int (73)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (412))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (446))
                                                                    (Prims.of_int (16)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    (Prims.strcat
                                                                    "num binders: "
                                                                    (Prims.string_of_int
                                                                    (FStar_List_Tot_Base.length
                                                                    brs)))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    match 
                                                                    (brs,
                                                                    (FStar_InteractiveHelpers_ExploreTerm.is_total_or_gtotal
                                                                    c))
                                                                    with
                                                                    | 
                                                                    (r::[],
                                                                    true) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (415))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (415))
                                                                    (Prims.of_int (29)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (416))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (416))
                                                                    (Prims.of_int (13)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    "PP_Pure"))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    PP_Pure)))
                                                                    | 
                                                                    (s1::r::s2::[],
                                                                    true) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (419))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (419))
                                                                    (Prims.of_int (33)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (420))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (443))
                                                                    (Prims.of_int (11)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Reflection_Derived.type_of_binder
                                                                    r))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun r_ty
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (420))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (420))
                                                                    (Prims.of_int (35)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (424))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (443))
                                                                    (Prims.of_int (11)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Reflection_Derived.type_of_binder
                                                                    s1))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    s1_ty ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (424))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (424))
                                                                    (Prims.of_int (54)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (425))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (443))
                                                                    (Prims.of_int (11)))
                                                                    (Obj.magic
                                                                    (opt_remove_refin
                                                                    (FStar_Reflection_Derived.type_of_binder
                                                                    s2)))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    s2_ty ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (425))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (425))
                                                                    (Prims.of_int (45)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (426))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (443))
                                                                    (Prims.of_int (11)))
                                                                    (Obj.magic
                                                                    (term_eq
                                                                    ret_type
                                                                    r_ty))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    ret_type_eq
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (426))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (426))
                                                                    (Prims.of_int (45)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (427))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (443))
                                                                    (Prims.of_int (11)))
                                                                    (Obj.magic
                                                                    (term_eq
                                                                    s1_ty
                                                                    s2_ty))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    state_type_eq
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (427))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (428))
                                                                    (Prims.of_int (59)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (429))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (443))
                                                                    (Prims.of_int (11)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (427))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (428))
                                                                    (Prims.of_int (59)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (427))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (428))
                                                                    (Prims.of_int (59)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (427))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (428))
                                                                    (Prims.of_int (58)))
                                                                    (Prims.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (427))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (427))
                                                                    (Prims.of_int (73)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (427))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (428))
                                                                    (Prims.of_int (58)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Builtins.term_to_string
                                                                    ret_type))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (428))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (428))
                                                                    (Prims.of_int (58)))
                                                                    (Prims.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (428))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (428))
                                                                    (Prims.of_int (58)))
                                                                    (Prims.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Builtins.term_to_string
                                                                    r_ty))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    Prims.strcat
                                                                    "\n-- binder: "
                                                                    uu___6))))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    Prims.strcat
                                                                    uu___5
                                                                    uu___6))))
                                                                    uu___5)))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Prims.strcat
                                                                    "- ret type:\n-- target: "
                                                                    uu___5))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    uu___5))
                                                                    uu___5)))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (429))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (430))
                                                                    (Prims.of_int (61)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (431))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (443))
                                                                    (Prims.of_int (11)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (429))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (430))
                                                                    (Prims.of_int (61)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (429))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (430))
                                                                    (Prims.of_int (61)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (429))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (430))
                                                                    (Prims.of_int (60)))
                                                                    (Prims.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (429))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (429))
                                                                    (Prims.of_int (74)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (429))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (430))
                                                                    (Prims.of_int (60)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Builtins.term_to_string
                                                                    s1_ty))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (430))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (430))
                                                                    (Prims.of_int (60)))
                                                                    (Prims.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (430))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (430))
                                                                    (Prims.of_int (60)))
                                                                    (Prims.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Builtins.term_to_string
                                                                    s2_ty))
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    Prims.strcat
                                                                    "\n-- binder2: "
                                                                    uu___7))))
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    Prims.strcat
                                                                    uu___6
                                                                    uu___7))))
                                                                    uu___6)))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    Prims.strcat
                                                                    "- state types:\n-- binder1: "
                                                                    uu___6))))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    uu___6))
                                                                    uu___6)))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (431))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (431))
                                                                    (Prims.of_int (74)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (432))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (443))
                                                                    (Prims.of_int (11)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    (Prims.strcat
                                                                    "- ret type equality: "
                                                                    (Prims.string_of_bool
                                                                    ret_type_eq))))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (432))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (432))
                                                                    (Prims.of_int (79)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (433))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (443))
                                                                    (Prims.of_int (11)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    (Prims.strcat
                                                                    "- state types equality: "
                                                                    (Prims.string_of_bool
                                                                    state_type_eq))))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    if
                                                                    ret_type_eq
                                                                    &&
                                                                    state_type_eq
                                                                    then
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (436))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (436))
                                                                    (Prims.of_int (71)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (437))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (437))
                                                                    (Prims.of_int (36)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (436))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (436))
                                                                    (Prims.of_int (71)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (436))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (436))
                                                                    (Prims.of_int (71)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (436))
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (436))
                                                                    (Prims.of_int (70)))
                                                                    (Prims.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Builtins.term_to_string
                                                                    (FStar_Reflection_Derived.type_of_binder
                                                                    s1)))
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    Prims.strcat
                                                                    "PP_State"
                                                                    uu___9))))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    uu___9))
                                                                    uu___9)))
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    PP_State
                                                                    (FStar_Reflection_Derived.type_of_binder
                                                                    s1))))
                                                                    else
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (441))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (441))
                                                                    (Prims.of_int (34)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (442))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (442))
                                                                    (Prims.of_int (18)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    "PP_Unknown"))
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    PP_Unknown))))
                                                                    uu___8)))
                                                                    uu___7)))
                                                                    uu___6)))
                                                                    uu___5)))
                                                                    uu___5)))
                                                                    uu___5)))
                                                                    uu___5)))
                                                                    uu___5)))
                                                                    uu___5))
                                                                    | 
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (445))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (445))
                                                                    (Prims.of_int (32)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (446))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (446))
                                                                    (Prims.of_int (16)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    "PP_Unknown"))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    PP_Unknown))))
                                                                    uu___4)))
                                                                 uu___3)))
                                                      uu___2))) uu___1)))
                            uu___1))) uu___)
let (check_pre_post_type :
  Prims.bool ->
    FStar_Reflection_Types.env ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.term ->
          FStar_Reflection_Types.term ->
            (pre_post_type, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun dbg ->
    fun e ->
      fun pre ->
        fun ret_type ->
          fun post ->
            FStar_Tactics_Effect.tac_bind
              (Prims.mk_range "FStar.InteractiveHelpers.Effectful.fst"
                 (Prims.of_int (450)) (Prims.of_int (2)) (Prims.of_int (450))
                 (Prims.of_int (40)))
              (Prims.mk_range "FStar.InteractiveHelpers.Effectful.fst"
                 (Prims.of_int (451)) (Prims.of_int (2)) (Prims.of_int (460))
                 (Prims.of_int (14)))
              (Obj.magic
                 (FStar_InteractiveHelpers_Base.print_dbg dbg
                    "[> check_pre_post_type"))
              (fun uu___ ->
                 (fun uu___ ->
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (Prims.mk_range
                            "FStar.InteractiveHelpers.Effectful.fst"
                            (Prims.of_int (451)) (Prims.of_int (8))
                            (Prims.of_int (451)) (Prims.of_int (73)))
                         (Prims.mk_range
                            "FStar.InteractiveHelpers.Effectful.fst"
                            (Prims.of_int (451)) (Prims.of_int (2))
                            (Prims.of_int (460)) (Prims.of_int (14)))
                         (Obj.magic
                            (FStar_Tactics_Effect.tac_bind
                               (Prims.mk_range
                                  "FStar.InteractiveHelpers.Effectful.fst"
                                  (Prims.of_int (451)) (Prims.of_int (8))
                                  (Prims.of_int (451)) (Prims.of_int (34)))
                               (Prims.mk_range
                                  "FStar.InteractiveHelpers.Effectful.fst"
                                  (Prims.of_int (451)) (Prims.of_int (8))
                                  (Prims.of_int (451)) (Prims.of_int (73)))
                               (Obj.magic (compute_pre_type dbg e pre))
                               (fun uu___1 ->
                                  (fun uu___1 ->
                                     Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (Prims.mk_range
                                             "FStar.InteractiveHelpers.Effectful.fst"
                                             (Prims.of_int (451))
                                             (Prims.of_int (36))
                                             (Prims.of_int (451))
                                             (Prims.of_int (73)))
                                          (Prims.mk_range
                                             "FStar.InteractiveHelpers.Effectful.fst"
                                             (Prims.of_int (451))
                                             (Prims.of_int (8))
                                             (Prims.of_int (451))
                                             (Prims.of_int (73)))
                                          (Obj.magic
                                             (compute_post_type dbg e
                                                ret_type post))
                                          (fun uu___2 ->
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___3 ->
                                                  (uu___1, uu___2))))) uu___1)))
                         (fun uu___1 ->
                            (fun uu___1 ->
                               match uu___1 with
                               | (PP_Pure, PP_Pure) ->
                                   Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (Prims.mk_range
                                           "FStar.InteractiveHelpers.Effectful.fst"
                                           (Prims.of_int (453))
                                           (Prims.of_int (4))
                                           (Prims.of_int (453))
                                           (Prims.of_int (36)))
                                        (Prims.mk_range
                                           "FStar.InteractiveHelpers.Effectful.fst"
                                           (Prims.of_int (454))
                                           (Prims.of_int (4))
                                           (Prims.of_int (454))
                                           (Prims.of_int (11)))
                                        (Obj.magic
                                           (FStar_InteractiveHelpers_Base.print_dbg
                                              dbg "PP_Pure, PP_Pure"))
                                        (fun uu___2 ->
                                           FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___3 -> PP_Pure)))
                               | (PP_State ty1, PP_State ty2) ->
                                   Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (Prims.mk_range
                                           "FStar.InteractiveHelpers.Effectful.fst"
                                           (Prims.of_int (456))
                                           (Prims.of_int (4))
                                           (Prims.of_int (456))
                                           (Prims.of_int (38)))
                                        (Prims.mk_range
                                           "FStar.InteractiveHelpers.Effectful.fst"
                                           (Prims.of_int (457))
                                           (Prims.of_int (4))
                                           (Prims.of_int (457))
                                           (Prims.of_int (56)))
                                        (Obj.magic
                                           (FStar_InteractiveHelpers_Base.print_dbg
                                              dbg "PP_State, PP_State"))
                                        (fun uu___2 ->
                                           (fun uu___2 ->
                                              Obj.magic
                                                (FStar_Tactics_Effect.tac_bind
                                                   (Prims.mk_range
                                                      "FStar.InteractiveHelpers.Effectful.fst"
                                                      (Prims.of_int (457))
                                                      (Prims.of_int (7))
                                                      (Prims.of_int (457))
                                                      (Prims.of_int (22)))
                                                   (Prims.mk_range
                                                      "FStar.InteractiveHelpers.Effectful.fst"
                                                      (Prims.of_int (457))
                                                      (Prims.of_int (4))
                                                      (Prims.of_int (457))
                                                      (Prims.of_int (56)))
                                                   (Obj.magic
                                                      (term_eq ty1 ty2))
                                                   (fun uu___3 ->
                                                      FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___4 ->
                                                           if uu___3
                                                           then PP_State ty1
                                                           else PP_Unknown))))
                                             uu___2))
                               | uu___2 ->
                                   Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (Prims.mk_range
                                           "FStar.InteractiveHelpers.Effectful.fst"
                                           (Prims.of_int (459))
                                           (Prims.of_int (4))
                                           (Prims.of_int (459))
                                           (Prims.of_int (24)))
                                        (Prims.mk_range
                                           "FStar.InteractiveHelpers.Effectful.fst"
                                           (Prims.of_int (460))
                                           (Prims.of_int (4))
                                           (Prims.of_int (460))
                                           (Prims.of_int (14)))
                                        (Obj.magic
                                           (FStar_InteractiveHelpers_Base.print_dbg
                                              dbg "_, _"))
                                        (fun uu___3 ->
                                           FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___4 -> PP_Unknown))))
                              uu___1))) uu___)
let (check_opt_pre_post_type :
  Prims.bool ->
    FStar_Reflection_Types.env ->
      FStar_Reflection_Types.term FStar_Pervasives_Native.option ->
        FStar_Reflection_Types.term ->
          FStar_Reflection_Types.term FStar_Pervasives_Native.option ->
            (pre_post_type FStar_Pervasives_Native.option, unit)
              FStar_Tactics_Effect.tac_repr)
  =
  fun dbg ->
    fun e ->
      fun opt_pre ->
        fun ret_type ->
          fun opt_post ->
            FStar_Tactics_Effect.tac_bind
              (Prims.mk_range "FStar.InteractiveHelpers.Effectful.fst"
                 (Prims.of_int (464)) (Prims.of_int (2)) (Prims.of_int (464))
                 (Prims.of_int (44)))
              (Prims.mk_range "FStar.InteractiveHelpers.Effectful.fst"
                 (Prims.of_int (465)) (Prims.of_int (2)) (Prims.of_int (477))
                 (Prims.of_int (8)))
              (Obj.magic
                 (FStar_InteractiveHelpers_Base.print_dbg dbg
                    "[> check_opt_pre_post_type"))
              (fun uu___ ->
                 (fun uu___ ->
                    match (opt_pre, opt_post) with
                    | (FStar_Pervasives_Native.Some pre,
                       FStar_Pervasives_Native.Some post) ->
                        Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (Prims.mk_range
                                "FStar.InteractiveHelpers.Effectful.fst"
                                (Prims.of_int (467)) (Prims.of_int (4))
                                (Prims.of_int (467)) (Prims.of_int (39)))
                             (Prims.mk_range
                                "FStar.InteractiveHelpers.Effectful.fst"
                                (Prims.of_int (468)) (Prims.of_int (4))
                                (Prims.of_int (468)) (Prims.of_int (54)))
                             (Obj.magic
                                (FStar_InteractiveHelpers_Base.print_dbg dbg
                                   "Some pre, Some post"))
                             (fun uu___1 ->
                                (fun uu___1 ->
                                   Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (Prims.mk_range
                                           "FStar.InteractiveHelpers.Effectful.fst"
                                           (Prims.of_int (468))
                                           (Prims.of_int (9))
                                           (Prims.of_int (468))
                                           (Prims.of_int (54)))
                                        (Prims.mk_range
                                           "FStar.InteractiveHelpers.Effectful.fst"
                                           (Prims.of_int (468))
                                           (Prims.of_int (4))
                                           (Prims.of_int (468))
                                           (Prims.of_int (54)))
                                        (Obj.magic
                                           (check_pre_post_type dbg e pre
                                              ret_type post))
                                        (fun uu___2 ->
                                           FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___3 ->
                                                FStar_Pervasives_Native.Some
                                                  uu___2)))) uu___1))
                    | (FStar_Pervasives_Native.Some pre,
                       FStar_Pervasives_Native.None) ->
                        Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (Prims.mk_range
                                "FStar.InteractiveHelpers.Effectful.fst"
                                (Prims.of_int (470)) (Prims.of_int (4))
                                (Prims.of_int (470)) (Prims.of_int (34)))
                             (Prims.mk_range
                                "FStar.InteractiveHelpers.Effectful.fst"
                                (Prims.of_int (471)) (Prims.of_int (4))
                                (Prims.of_int (471)) (Prims.of_int (37)))
                             (Obj.magic
                                (FStar_InteractiveHelpers_Base.print_dbg dbg
                                   "Some pre, None"))
                             (fun uu___1 ->
                                (fun uu___1 ->
                                   Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (Prims.mk_range
                                           "FStar.InteractiveHelpers.Effectful.fst"
                                           (Prims.of_int (471))
                                           (Prims.of_int (9))
                                           (Prims.of_int (471))
                                           (Prims.of_int (37)))
                                        (Prims.mk_range
                                           "FStar.InteractiveHelpers.Effectful.fst"
                                           (Prims.of_int (471))
                                           (Prims.of_int (4))
                                           (Prims.of_int (471))
                                           (Prims.of_int (37)))
                                        (Obj.magic
                                           (compute_pre_type dbg e pre))
                                        (fun uu___2 ->
                                           FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___3 ->
                                                FStar_Pervasives_Native.Some
                                                  uu___2)))) uu___1))
                    | (FStar_Pervasives_Native.None,
                       FStar_Pervasives_Native.Some post) ->
                        Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (Prims.mk_range
                                "FStar.InteractiveHelpers.Effectful.fst"
                                (Prims.of_int (473)) (Prims.of_int (4))
                                (Prims.of_int (473)) (Prims.of_int (35)))
                             (Prims.mk_range
                                "FStar.InteractiveHelpers.Effectful.fst"
                                (Prims.of_int (474)) (Prims.of_int (4))
                                (Prims.of_int (474)) (Prims.of_int (48)))
                             (Obj.magic
                                (FStar_InteractiveHelpers_Base.print_dbg dbg
                                   "None, Some post"))
                             (fun uu___1 ->
                                (fun uu___1 ->
                                   Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (Prims.mk_range
                                           "FStar.InteractiveHelpers.Effectful.fst"
                                           (Prims.of_int (474))
                                           (Prims.of_int (9))
                                           (Prims.of_int (474))
                                           (Prims.of_int (48)))
                                        (Prims.mk_range
                                           "FStar.InteractiveHelpers.Effectful.fst"
                                           (Prims.of_int (474))
                                           (Prims.of_int (4))
                                           (Prims.of_int (474))
                                           (Prims.of_int (48)))
                                        (Obj.magic
                                           (compute_post_type dbg e ret_type
                                              post))
                                        (fun uu___2 ->
                                           FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___3 ->
                                                FStar_Pervasives_Native.Some
                                                  uu___2)))) uu___1))
                    | (FStar_Pervasives_Native.None,
                       FStar_Pervasives_Native.None) ->
                        Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (Prims.mk_range
                                "FStar.InteractiveHelpers.Effectful.fst"
                                (Prims.of_int (476)) (Prims.of_int (4))
                                (Prims.of_int (476)) (Prims.of_int (30)))
                             (Prims.mk_range
                                "FStar.InteractiveHelpers.Effectful.fst"
                                (Prims.of_int (477)) (Prims.of_int (4))
                                (Prims.of_int (477)) (Prims.of_int (8)))
                             (Obj.magic
                                (FStar_InteractiveHelpers_Base.print_dbg dbg
                                   "None, None"))
                             (fun uu___1 ->
                                FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___2 -> FStar_Pervasives_Native.None))))
                   uu___)
let rec (_introduce_variables_for_abs :
  FStar_InteractiveHelpers_Base.genv ->
    FStar_Reflection_Types.typ ->
      ((FStar_Reflection_Types.term Prims.list *
         FStar_Reflection_Types.binder Prims.list *
         FStar_InteractiveHelpers_Base.genv),
        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun ge ->
    fun ty ->
      FStar_Tactics_Effect.tac_bind
        (Prims.mk_range "FStar.InteractiveHelpers.Effectful.fst"
           (Prims.of_int (481)) (Prims.of_int (8)) (Prims.of_int (481))
           (Prims.of_int (18)))
        (Prims.mk_range "FStar.InteractiveHelpers.Effectful.fst"
           (Prims.of_int (481)) (Prims.of_int (2)) (Prims.of_int (492))
           (Prims.of_int (18)))
        (Obj.magic (FStar_Tactics_Builtins.inspect ty))
        (fun uu___ ->
           (fun uu___ ->
              match uu___ with
              | FStar_Reflection_Data.Tv_Arrow (b, c) ->
                  Obj.magic
                    (Obj.repr
                       (FStar_Tactics_Effect.tac_bind
                          (Prims.mk_range
                             "FStar.InteractiveHelpers.Effectful.fst"
                             (Prims.of_int (483)) (Prims.of_int (18))
                             (Prims.of_int (483)) (Prims.of_int (88)))
                          (Prims.mk_range
                             "FStar.InteractiveHelpers.Effectful.fst"
                             (Prims.of_int (483)) (Prims.of_int (4))
                             (Prims.of_int (491)) (Prims.of_int (7)))
                          (Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (Prims.mk_range
                                   "FStar.InteractiveHelpers.Effectful.fst"
                                   (Prims.of_int (483)) (Prims.of_int (44))
                                   (Prims.of_int (483)) (Prims.of_int (69)))
                                (Prims.mk_range
                                   "FStar.InteractiveHelpers.Effectful.fst"
                                   (Prims.of_int (483)) (Prims.of_int (18))
                                   (Prims.of_int (483)) (Prims.of_int (88)))
                                (Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (Prims.mk_range
                                         "FStar.InteractiveHelpers.Effectful.fst"
                                         (Prims.of_int (483))
                                         (Prims.of_int (52))
                                         (Prims.of_int (483))
                                         (Prims.of_int (68)))
                                      (Prims.mk_range "prims.fst"
                                         (Prims.of_int (606))
                                         (Prims.of_int (19))
                                         (Prims.of_int (606))
                                         (Prims.of_int (31)))
                                      (Obj.magic
                                         (FStar_Tactics_Derived.name_of_binder
                                            b))
                                      (fun uu___1 ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___2 ->
                                              Prims.strcat "__" uu___1))))
                                (fun uu___1 ->
                                   (fun uu___1 ->
                                      Obj.magic
                                        (FStar_InteractiveHelpers_Base.genv_push_fresh_binder
                                           ge uu___1
                                           (FStar_Reflection_Derived.type_of_binder
                                              b))) uu___1)))
                          (fun uu___1 ->
                             (fun uu___1 ->
                                match uu___1 with
                                | (ge1, b1) ->
                                    Obj.magic
                                      (FStar_Tactics_Effect.tac_bind
                                         (Prims.mk_range
                                            "FStar.InteractiveHelpers.Effectful.fst"
                                            (Prims.of_int (484))
                                            (Prims.of_int (14))
                                            (Prims.of_int (484))
                                            (Prims.of_int (29)))
                                         (Prims.mk_range
                                            "FStar.InteractiveHelpers.Effectful.fst"
                                            (Prims.of_int (485))
                                            (Prims.of_int (4))
                                            (Prims.of_int (491))
                                            (Prims.of_int (7)))
                                         (FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___2 ->
                                               FStar_Reflection_Derived.bv_of_binder
                                                 b1))
                                         (fun uu___2 ->
                                            (fun bv1 ->
                                               Obj.magic
                                                 (FStar_Tactics_Effect.tac_bind
                                                    (Prims.mk_range
                                                       "FStar.InteractiveHelpers.Effectful.fst"
                                                       (Prims.of_int (485))
                                                       (Prims.of_int (13))
                                                       (Prims.of_int (485))
                                                       (Prims.of_int (30)))
                                                    (Prims.mk_range
                                                       "FStar.InteractiveHelpers.Effectful.fst"
                                                       (Prims.of_int (486))
                                                       (Prims.of_int (10))
                                                       (Prims.of_int (490))
                                                       (Prims.of_int (29)))
                                                    (Obj.magic
                                                       (FStar_Tactics_Builtins.pack
                                                          (FStar_Reflection_Data.Tv_Var
                                                             bv1)))
                                                    (fun uu___2 ->
                                                       (fun v1 ->
                                                          match FStar_InteractiveHelpers_ExploreTerm.get_total_or_gtotal_ret_type
                                                                  c
                                                          with
                                                          | FStar_Pervasives_Native.Some
                                                              ty1 ->
                                                              Obj.magic
                                                                (Obj.repr
                                                                   (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (488))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (488))
                                                                    (Prims.of_int (60)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (488))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (489))
                                                                    (Prims.of_int (29)))
                                                                    (Obj.magic
                                                                    (_introduce_variables_for_abs
                                                                    ge1 ty1))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___2
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
                                                                    uu___2 ->
                                                                    ([v1],
                                                                    [b1],
                                                                    ge1)))))
                                                         uu___2))) uu___2)))
                               uu___1)))
              | uu___1 ->
                  Obj.magic
                    (Obj.repr
                       (FStar_Tactics_Effect.lift_div_tac
                          (fun uu___2 -> ([], [], ge))))) uu___)
let (introduce_variables_for_abs :
  FStar_InteractiveHelpers_Base.genv ->
    FStar_Reflection_Types.term ->
      ((FStar_Reflection_Types.term Prims.list *
         FStar_Reflection_Types.binder Prims.list *
         FStar_InteractiveHelpers_Base.genv),
        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun ge ->
    fun tm ->
      FStar_Tactics_Effect.tac_bind
        (Prims.mk_range "FStar.InteractiveHelpers.Effectful.fst"
           (Prims.of_int (496)) (Prims.of_int (8)) (Prims.of_int (496))
           (Prims.of_int (25)))
        (Prims.mk_range "FStar.InteractiveHelpers.Effectful.fst"
           (Prims.of_int (496)) (Prims.of_int (2)) (Prims.of_int (498))
           (Prims.of_int (22)))
        (Obj.magic
           (FStar_InteractiveHelpers_ExploreTerm.safe_tc
              ge.FStar_InteractiveHelpers_Base.env tm))
        (fun uu___ ->
           (fun uu___ ->
              match uu___ with
              | FStar_Pervasives_Native.Some ty ->
                  Obj.magic (Obj.repr (_introduce_variables_for_abs ge ty))
              | FStar_Pervasives_Native.None ->
                  Obj.magic
                    (Obj.repr
                       (FStar_Tactics_Effect.lift_div_tac
                          (fun uu___1 -> ([], [], ge))))) uu___)
let (introduce_variables_for_opt_abs :
  FStar_InteractiveHelpers_Base.genv ->
    FStar_Reflection_Types.term FStar_Pervasives_Native.option ->
      ((FStar_Reflection_Types.term Prims.list *
         FStar_Reflection_Types.binder Prims.list *
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
    FStar_Reflection_Types.term ->
      (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun dbg ->
    fun t ->
      FStar_Tactics_Effect.tac_bind
        (Prims.mk_range "FStar.InteractiveHelpers.Effectful.fst"
           (Prims.of_int (514)) (Prims.of_int (2)) (Prims.of_int (514))
           (Prims.of_int (54)))
        (Prims.mk_range "FStar.InteractiveHelpers.Effectful.fst"
           (Prims.of_int (515)) (Prims.of_int (2)) (Prims.of_int (528))
           (Prims.of_int (9)))
        (Obj.magic
           (FStar_Tactics_Effect.tac_bind
              (Prims.mk_range "FStar.InteractiveHelpers.Effectful.fst"
                 (Prims.of_int (514)) (Prims.of_int (16))
                 (Prims.of_int (514)) (Prims.of_int (54)))
              (Prims.mk_range "FStar.InteractiveHelpers.Effectful.fst"
                 (Prims.of_int (514)) (Prims.of_int (2)) (Prims.of_int (514))
                 (Prims.of_int (54)))
              (Obj.magic
                 (FStar_Tactics_Effect.tac_bind
                    (Prims.mk_range "FStar.InteractiveHelpers.Effectful.fst"
                       (Prims.of_int (514)) (Prims.of_int (37))
                       (Prims.of_int (514)) (Prims.of_int (53)))
                    (Prims.mk_range "prims.fst" (Prims.of_int (606))
                       (Prims.of_int (19)) (Prims.of_int (606))
                       (Prims.of_int (31)))
                    (Obj.magic (FStar_Tactics_Builtins.term_to_string t))
                    (fun uu___ ->
                       FStar_Tactics_Effect.lift_div_tac
                         (fun uu___1 -> Prims.strcat "[> is_st_get:\n" uu___))))
              (fun uu___ ->
                 (fun uu___ ->
                    Obj.magic
                      (FStar_InteractiveHelpers_Base.print_dbg dbg uu___))
                   uu___)))
        (fun uu___ ->
           (fun uu___ ->
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (Prims.mk_range "FStar.InteractiveHelpers.Effectful.fst"
                      (Prims.of_int (515)) (Prims.of_int (8))
                      (Prims.of_int (515)) (Prims.of_int (17)))
                   (Prims.mk_range "FStar.InteractiveHelpers.Effectful.fst"
                      (Prims.of_int (515)) (Prims.of_int (2))
                      (Prims.of_int (528)) (Prims.of_int (9)))
                   (Obj.magic (FStar_Tactics_Builtins.inspect t))
                   (fun uu___1 ->
                      (fun uu___1 ->
                         match uu___1 with
                         | FStar_Reflection_Data.Tv_App (hd, (a, qual)) ->
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (Prims.mk_range
                                     "FStar.InteractiveHelpers.Effectful.fst"
                                     (Prims.of_int (517)) (Prims.of_int (4))
                                     (Prims.of_int (517)) (Prims.of_int (32)))
                                  (Prims.mk_range
                                     "FStar.InteractiveHelpers.Effectful.fst"
                                     (Prims.of_int (518)) (Prims.of_int (10))
                                     (Prims.of_int (524)) (Prims.of_int (11)))
                                  (Obj.magic
                                     (FStar_InteractiveHelpers_Base.print_dbg
                                        dbg "-> Is Tv_App"))
                                  (fun uu___2 ->
                                     (fun uu___2 ->
                                        Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (Prims.mk_range
                                                "FStar.InteractiveHelpers.Effectful.fst"
                                                (Prims.of_int (518))
                                                (Prims.of_int (16))
                                                (Prims.of_int (518))
                                                (Prims.of_int (26)))
                                             (Prims.mk_range
                                                "FStar.InteractiveHelpers.Effectful.fst"
                                                (Prims.of_int (518))
                                                (Prims.of_int (10))
                                                (Prims.of_int (524))
                                                (Prims.of_int (11)))
                                             (Obj.magic
                                                (FStar_Tactics_Builtins.inspect
                                                   hd))
                                             (fun uu___3 ->
                                                (fun uu___3 ->
                                                   match uu___3 with
                                                   | FStar_Reflection_Data.Tv_FVar
                                                       fv ->
                                                       Obj.magic
                                                         (FStar_Tactics_Effect.tac_bind
                                                            (Prims.mk_range
                                                               "FStar.InteractiveHelpers.Effectful.fst"
                                                               (Prims.of_int (520))
                                                               (Prims.of_int (6))
                                                               (Prims.of_int (520))
                                                               (Prims.of_int (62)))
                                                            (Prims.mk_range
                                                               "FStar.InteractiveHelpers.Effectful.fst"
                                                               (Prims.of_int (521))
                                                               (Prims.of_int (6))
                                                               (Prims.of_int (521))
                                                               (Prims.of_int (56)))
                                                            (Obj.magic
                                                               (FStar_InteractiveHelpers_Base.print_dbg
                                                                  dbg
                                                                  (Prims.strcat
                                                                    "-> Head is Tv_FVar: "
                                                                    (FStar_Reflection_Derived.fv_to_string
                                                                    fv))))
                                                            (fun uu___4 ->
                                                               FStar_Tactics_Effect.lift_div_tac
                                                                 (fun uu___5
                                                                    ->
                                                                    FStar_InteractiveHelpers_Base.fv_eq_name
                                                                    fv
                                                                    ["FStar";
                                                                    "HyperStack";
                                                                    "ST";
                                                                    "get"])))
                                                   | uu___4 ->
                                                       Obj.magic
                                                         (FStar_Tactics_Effect.tac_bind
                                                            (Prims.mk_range
                                                               "FStar.InteractiveHelpers.Effectful.fst"
                                                               (Prims.of_int (523))
                                                               (Prims.of_int (6))
                                                               (Prims.of_int (523))
                                                               (Prims.of_int (44)))
                                                            (Prims.mk_range
                                                               "FStar.InteractiveHelpers.Effectful.fst"
                                                               (Prims.of_int (524))
                                                               (Prims.of_int (6))
                                                               (Prims.of_int (524))
                                                               (Prims.of_int (11)))
                                                            (Obj.magic
                                                               (FStar_InteractiveHelpers_Base.print_dbg
                                                                  dbg
                                                                  "-> Head is not Tv_FVar"))
                                                            (fun uu___5 ->
                                                               FStar_Tactics_Effect.lift_div_tac
                                                                 (fun uu___6
                                                                    -> false))))
                                                  uu___3))) uu___2))
                         | uu___2 ->
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (Prims.mk_range
                                     "FStar.InteractiveHelpers.Effectful.fst"
                                     (Prims.of_int (527)) (Prims.of_int (4))
                                     (Prims.of_int (527)) (Prims.of_int (36)))
                                  (Prims.mk_range
                                     "FStar.InteractiveHelpers.Effectful.fst"
                                     (Prims.of_int (528)) (Prims.of_int (4))
                                     (Prims.of_int (528)) (Prims.of_int (9)))
                                  (Obj.magic
                                     (FStar_InteractiveHelpers_Base.print_dbg
                                        dbg "-> Is not Tv_App"))
                                  (fun uu___3 ->
                                     FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___4 -> false)))) uu___1)))
             uu___)
let (is_let_st_get :
  Prims.bool ->
    FStar_Reflection_Data.term_view ->
      (FStar_Reflection_Types.bv FStar_Pervasives_Native.option, unit)
        FStar_Tactics_Effect.tac_repr)
  =
  fun dbg ->
    fun t ->
      FStar_Tactics_Effect.tac_bind
        (Prims.mk_range "FStar.InteractiveHelpers.Effectful.fst"
           (Prims.of_int (531)) (Prims.of_int (2)) (Prims.of_int (531))
           (Prims.of_int (58)))
        (Prims.mk_range "FStar.InteractiveHelpers.Effectful.fst"
           (Prims.of_int (532)) (Prims.of_int (2)) (Prims.of_int (538))
           (Prims.of_int (8)))
        (Obj.magic
           (FStar_Tactics_Effect.tac_bind
              (Prims.mk_range "FStar.InteractiveHelpers.Effectful.fst"
                 (Prims.of_int (531)) (Prims.of_int (16))
                 (Prims.of_int (531)) (Prims.of_int (58)))
              (Prims.mk_range "FStar.InteractiveHelpers.Effectful.fst"
                 (Prims.of_int (531)) (Prims.of_int (2)) (Prims.of_int (531))
                 (Prims.of_int (58)))
              (Obj.magic
                 (FStar_Tactics_Effect.tac_bind
                    (Prims.mk_range "FStar.InteractiveHelpers.Effectful.fst"
                       (Prims.of_int (531)) (Prims.of_int (41))
                       (Prims.of_int (531)) (Prims.of_int (57)))
                    (Prims.mk_range "prims.fst" (Prims.of_int (606))
                       (Prims.of_int (19)) (Prims.of_int (606))
                       (Prims.of_int (31)))
                    (Obj.magic
                       (FStar_Tactics_Effect.tac_bind
                          (Prims.mk_range
                             "FStar.InteractiveHelpers.Effectful.fst"
                             (Prims.of_int (530)) (Prims.of_int (23))
                             (Prims.of_int (530)) (Prims.of_int (24)))
                          (Prims.mk_range
                             "FStar.InteractiveHelpers.Effectful.fst"
                             (Prims.of_int (531)) (Prims.of_int (41))
                             (Prims.of_int (531)) (Prims.of_int (57)))
                          (Obj.magic (FStar_Tactics_Builtins.pack t))
                          (fun uu___ ->
                             (fun uu___ ->
                                Obj.magic
                                  (FStar_Tactics_Builtins.term_to_string
                                     uu___)) uu___)))
                    (fun uu___ ->
                       FStar_Tactics_Effect.lift_div_tac
                         (fun uu___1 ->
                            Prims.strcat "[> is_let_st_get:\n" uu___))))
              (fun uu___ ->
                 (fun uu___ ->
                    Obj.magic
                      (FStar_InteractiveHelpers_Base.print_dbg dbg uu___))
                   uu___)))
        (fun uu___ ->
           (fun uu___ ->
              match t with
              | FStar_Reflection_Data.Tv_Let (recf, attrs, bv, def, body) ->
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (Prims.mk_range
                          "FStar.InteractiveHelpers.Effectful.fst"
                          (Prims.of_int (534)) (Prims.of_int (4))
                          (Prims.of_int (534)) (Prims.of_int (48)))
                       (Prims.mk_range
                          "FStar.InteractiveHelpers.Effectful.fst"
                          (Prims.of_int (535)) (Prims.of_int (4))
                          (Prims.of_int (535)) (Prims.of_int (47)))
                       (Obj.magic
                          (FStar_InteractiveHelpers_Base.print_dbg dbg
                             "The term is a let expression"))
                       (fun uu___1 ->
                          (fun uu___1 ->
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (Prims.mk_range
                                     "FStar.InteractiveHelpers.Effectful.fst"
                                     (Prims.of_int (535)) (Prims.of_int (7))
                                     (Prims.of_int (535)) (Prims.of_int (24)))
                                  (Prims.mk_range
                                     "FStar.InteractiveHelpers.Effectful.fst"
                                     (Prims.of_int (535)) (Prims.of_int (4))
                                     (Prims.of_int (535)) (Prims.of_int (47)))
                                  (Obj.magic (is_st_get dbg def))
                                  (fun uu___2 ->
                                     FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___3 ->
                                          if uu___2
                                          then
                                            FStar_Pervasives_Native.Some bv
                                          else FStar_Pervasives_Native.None))))
                            uu___1))
              | uu___1 ->
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (Prims.mk_range
                          "FStar.InteractiveHelpers.Effectful.fst"
                          (Prims.of_int (537)) (Prims.of_int (4))
                          (Prims.of_int (537)) (Prims.of_int (52)))
                       (Prims.mk_range
                          "FStar.InteractiveHelpers.Effectful.fst"
                          (Prims.of_int (538)) (Prims.of_int (4))
                          (Prims.of_int (538)) (Prims.of_int (8)))
                       (Obj.magic
                          (FStar_InteractiveHelpers_Base.print_dbg dbg
                             "The term is not a let expression"))
                       (fun uu___2 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___3 -> FStar_Pervasives_Native.None))))
             uu___)
let (term_has_effectful_comp :
  Prims.bool ->
    FStar_Reflection_Types.env ->
      FStar_Reflection_Types.term ->
        (Prims.bool FStar_Pervasives_Native.option, unit)
          FStar_Tactics_Effect.tac_repr)
  =
  fun dbg ->
    fun e ->
      fun tm ->
        FStar_Tactics_Effect.tac_bind
          (Prims.mk_range "FStar.InteractiveHelpers.Effectful.fst"
             (Prims.of_int (550)) (Prims.of_int (2)) (Prims.of_int (550))
             (Prims.of_int (44)))
          (Prims.mk_range "FStar.InteractiveHelpers.Effectful.fst"
             (Prims.of_int (551)) (Prims.of_int (2)) (Prims.of_int (558))
             (Prims.of_int (8)))
          (Obj.magic
             (FStar_InteractiveHelpers_Base.print_dbg dbg
                "[> term_has_effectful_comp"))
          (fun uu___ ->
             (fun uu___ ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (Prims.mk_range "FStar.InteractiveHelpers.Effectful.fst"
                        (Prims.of_int (551)) (Prims.of_int (18))
                        (Prims.of_int (551)) (Prims.of_int (46)))
                     (Prims.mk_range "FStar.InteractiveHelpers.Effectful.fst"
                        (Prims.of_int (552)) (Prims.of_int (2))
                        (Prims.of_int (558)) (Prims.of_int (8)))
                     (Obj.magic (compute_effect_info dbg e tm))
                     (fun uu___1 ->
                        (fun einfo_opt ->
                           match einfo_opt with
                           | FStar_Pervasives_Native.Some einfo ->
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (Prims.mk_range
                                       "FStar.InteractiveHelpers.Effectful.fst"
                                       (Prims.of_int (554))
                                       (Prims.of_int (4))
                                       (Prims.of_int (554))
                                       (Prims.of_int (73)))
                                    (Prims.mk_range
                                       "FStar.InteractiveHelpers.Effectful.fst"
                                       (Prims.of_int (555))
                                       (Prims.of_int (4))
                                       (Prims.of_int (555))
                                       (Prims.of_int (50)))
                                    (Obj.magic
                                       (FStar_InteractiveHelpers_Base.print_dbg
                                          dbg
                                          (Prims.strcat "Effect type: "
                                             (FStar_InteractiveHelpers_ExploreTerm.effect_type_to_string
                                                einfo.ei_type))))
                                    (fun uu___1 ->
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___2 ->
                                            FStar_Pervasives_Native.Some
                                              (Prims.op_Negation
                                                 (FStar_InteractiveHelpers_ExploreTerm.effect_type_is_pure
                                                    einfo.ei_type)))))
                           | FStar_Pervasives_Native.None ->
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (Prims.mk_range
                                       "FStar.InteractiveHelpers.Effectful.fst"
                                       (Prims.of_int (557))
                                       (Prims.of_int (4))
                                       (Prims.of_int (557))
                                       (Prims.of_int (49)))
                                    (Prims.mk_range
                                       "FStar.InteractiveHelpers.Effectful.fst"
                                       (Prims.of_int (558))
                                       (Prims.of_int (4))
                                       (Prims.of_int (558))
                                       (Prims.of_int (8)))
                                    (Obj.magic
                                       (FStar_InteractiveHelpers_Base.print_dbg
                                          dbg "Could not compute effect info"))
                                    (fun uu___1 ->
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___2 ->
                                            FStar_Pervasives_Native.None))))
                          uu___1))) uu___)
let (related_term_is_effectul :
  Prims.bool ->
    FStar_InteractiveHelpers_Base.genv ->
      FStar_Reflection_Data.term_view ->
        (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun dbg ->
    fun ge ->
      fun tv ->
        FStar_Tactics_Effect.tac_bind
          (Prims.mk_range "FStar.InteractiveHelpers.Effectful.fst"
             (Prims.of_int (570)) (Prims.of_int (4)) (Prims.of_int (570))
             (Prims.of_int (55)))
          (Prims.mk_range "FStar.InteractiveHelpers.Effectful.fst"
             (Prims.of_int (572)) (Prims.of_int (2)) (Prims.of_int (594))
             (Prims.of_int (45)))
          (FStar_Tactics_Effect.lift_div_tac
             (fun uu___ ->
                fun tm ->
                  FStar_Tactics_Effect.tac_bind
                    (Prims.mk_range "FStar.InteractiveHelpers.Effectful.fst"
                       (Prims.of_int (570)) (Prims.of_int (4))
                       (Prims.of_int (570)) (Prims.of_int (41)))
                    (Prims.mk_range "FStar.InteractiveHelpers.Effectful.fst"
                       (Prims.of_int (570)) (Prims.of_int (4))
                       (Prims.of_int (570)) (Prims.of_int (55)))
                    (Obj.magic
                       (term_has_effectful_comp dbg
                          ge.FStar_InteractiveHelpers_Base.env tm))
                    (fun uu___1 ->
                       FStar_Tactics_Effect.lift_div_tac
                         (fun uu___2 ->
                            uu___1 <> (FStar_Pervasives_Native.Some false)))))
          (fun uu___ ->
             (fun is_effectful ->
                match tv with
                | FStar_Reflection_Data.Tv_Var uu___ ->
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___1 -> false)))
                | FStar_Reflection_Data.Tv_BVar uu___ ->
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___1 -> false)))
                | FStar_Reflection_Data.Tv_FVar uu___ ->
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___1 -> false)))
                | FStar_Reflection_Data.Tv_App (hd, (a, qual)) ->
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___ -> false)))
                | FStar_Reflection_Data.Tv_Abs (br, body) ->
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___ -> false)))
                | FStar_Reflection_Data.Tv_Arrow (br, c0) ->
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___ -> false)))
                | FStar_Reflection_Data.Tv_Type uu___ ->
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___1 -> false)))
                | FStar_Reflection_Data.Tv_Refine (bv, ref) ->
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___ -> false)))
                | FStar_Reflection_Data.Tv_Const uu___ ->
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___1 -> false)))
                | FStar_Reflection_Data.Tv_Uvar (uu___, uu___1) ->
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___2 -> false)))
                | FStar_Reflection_Data.Tv_Let (recf, attrs, bv, def, body)
                    -> Obj.magic (Obj.repr (is_effectful def))
                | FStar_Reflection_Data.Tv_Match
                    (scrutinee, _ret_opt, branches) ->
                    Obj.magic (Obj.repr (is_effectful scrutinee))
                | FStar_Reflection_Data.Tv_AscribedT (e, ty, tac, uu___) ->
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___1 -> false)))
                | FStar_Reflection_Data.Tv_AscribedC (e, c, tac, uu___) ->
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___1 -> false)))
                | uu___ ->
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___1 -> true)))) uu___)
let rec (find_mem_in_related :
  Prims.bool ->
    FStar_InteractiveHelpers_Base.genv ->
      FStar_Reflection_Data.term_view Prims.list ->
        (FStar_Reflection_Types.bv FStar_Pervasives_Native.option, unit)
          FStar_Tactics_Effect.tac_repr)
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
                        (FStar_Tactics_Effect.tac_bind
                           (Prims.mk_range
                              "FStar.InteractiveHelpers.Effectful.fst"
                              (Prims.of_int (612)) (Prims.of_int (4))
                              (Prims.of_int (612)) (Prims.of_int (67)))
                           (Prims.mk_range
                              "FStar.InteractiveHelpers.Effectful.fst"
                              (Prims.of_int (613)) (Prims.of_int (4))
                              (Prims.of_int (629)) (Prims.of_int (11)))
                           (Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (Prims.mk_range
                                    "FStar.InteractiveHelpers.Effectful.fst"
                                    (Prims.of_int (612)) (Prims.of_int (18))
                                    (Prims.of_int (612)) (Prims.of_int (67)))
                                 (Prims.mk_range
                                    "FStar.InteractiveHelpers.Effectful.fst"
                                    (Prims.of_int (612)) (Prims.of_int (4))
                                    (Prims.of_int (612)) (Prims.of_int (67)))
                                 (Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (Prims.mk_range
                                          "FStar.InteractiveHelpers.Effectful.fst"
                                          (Prims.of_int (612))
                                          (Prims.of_int (49))
                                          (Prims.of_int (612))
                                          (Prims.of_int (66)))
                                       (Prims.mk_range "prims.fst"
                                          (Prims.of_int (606))
                                          (Prims.of_int (19))
                                          (Prims.of_int (606))
                                          (Prims.of_int (31)))
                                       (Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (Prims.mk_range
                                                "FStar.InteractiveHelpers.Effectful.fst"
                                                (Prims.of_int (611))
                                                (Prims.of_int (4))
                                                (Prims.of_int (611))
                                                (Prims.of_int (6)))
                                             (Prims.mk_range
                                                "FStar.InteractiveHelpers.Effectful.fst"
                                                (Prims.of_int (612))
                                                (Prims.of_int (49))
                                                (Prims.of_int (612))
                                                (Prims.of_int (66)))
                                             (Obj.magic
                                                (FStar_Tactics_Builtins.pack
                                                   tv))
                                             (fun uu___ ->
                                                (fun uu___ ->
                                                   Obj.magic
                                                     (FStar_Tactics_Builtins.term_to_string
                                                        uu___)) uu___)))
                                       (fun uu___ ->
                                          FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___1 ->
                                               Prims.strcat
                                                 "[> find_mem_in_related:\n"
                                                 uu___))))
                                 (fun uu___ ->
                                    (fun uu___ ->
                                       Obj.magic
                                         (FStar_InteractiveHelpers_Base.print_dbg
                                            dbg uu___)) uu___)))
                           (fun uu___ ->
                              (fun uu___ ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (Prims.mk_range
                                         "FStar.InteractiveHelpers.Effectful.fst"
                                         (Prims.of_int (613))
                                         (Prims.of_int (10))
                                         (Prims.of_int (613))
                                         (Prims.of_int (30)))
                                      (Prims.mk_range
                                         "FStar.InteractiveHelpers.Effectful.fst"
                                         (Prims.of_int (613))
                                         (Prims.of_int (4))
                                         (Prims.of_int (629))
                                         (Prims.of_int (11)))
                                      (Obj.magic (is_let_st_get dbg tv))
                                      (fun uu___1 ->
                                         (fun uu___1 ->
                                            match uu___1 with
                                            | FStar_Pervasives_Native.Some bv
                                                ->
                                                Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (Prims.mk_range
                                                        "FStar.InteractiveHelpers.Effectful.fst"
                                                        (Prims.of_int (615))
                                                        (Prims.of_int (6))
                                                        (Prims.of_int (615))
                                                        (Prims.of_int (87)))
                                                     (Prims.mk_range
                                                        "FStar.InteractiveHelpers.Effectful.fst"
                                                        (Prims.of_int (616))
                                                        (Prims.of_int (6))
                                                        (Prims.of_int (616))
                                                        (Prims.of_int (13)))
                                                     (Obj.magic
                                                        (FStar_InteractiveHelpers_Base.print_dbg
                                                           dbg
                                                           "Term is of the form `let x = FStar.HyperStack.ST.get ()`: success"))
                                                     (fun uu___2 ->
                                                        FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___3 ->
                                                             FStar_Pervasives_Native.Some
                                                               bv)))
                                            | FStar_Pervasives_Native.None ->
                                                Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (Prims.mk_range
                                                        "FStar.InteractiveHelpers.Effectful.fst"
                                                        (Prims.of_int (618))
                                                        (Prims.of_int (6))
                                                        (Prims.of_int (618))
                                                        (Prims.of_int (94)))
                                                     (Prims.mk_range
                                                        "FStar.InteractiveHelpers.Effectful.fst"
                                                        (Prims.of_int (619))
                                                        (Prims.of_int (6))
                                                        (Prims.of_int (629))
                                                        (Prims.of_int (11)))
                                                     (Obj.magic
                                                        (FStar_InteractiveHelpers_Base.print_dbg
                                                           dbg
                                                           "Term is not of the form `let x = FStar.HyperStack.ST.get ()`: continuing"))
                                                     (fun uu___2 ->
                                                        (fun uu___2 ->
                                                           Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (Prims.mk_range
                                                                   "FStar.InteractiveHelpers.Effectful.fst"
                                                                   (Prims.of_int (619))
                                                                   (Prims.of_int (9))
                                                                   (Prims.of_int (619))
                                                                   (Prims.of_int (43)))
                                                                (Prims.mk_range
                                                                   "FStar.InteractiveHelpers.Effectful.fst"
                                                                   (Prims.of_int (619))
                                                                   (Prims.of_int (6))
                                                                   (Prims.of_int (629))
                                                                   (Prims.of_int (11)))
                                                                (Obj.magic
                                                                   (related_term_is_effectul
                                                                    dbg ge tv))
                                                                (fun uu___3
                                                                   ->
                                                                   (fun
                                                                    uu___3 ->
                                                                    if uu___3
                                                                    then
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (622))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (622))
                                                                    (Prims.of_int (56)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (623))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (623))
                                                                    (Prims.of_int (12)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    "Term is effectful: stopping here"))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Pervasives_Native.None)))
                                                                    else
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (627))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (627))
                                                                    (Prims.of_int (57)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (628))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (628))
                                                                    (Prims.of_int (39)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    "Term is not effectful: continuing"))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (find_mem_in_related
                                                                    dbg ge
                                                                    tms'))
                                                                    uu___5)))
                                                                    uu___3)))
                                                          uu___2))) uu___1)))
                                uu___)))) uu___2 uu___1 uu___
let rec (find_mem_in_children :
  Prims.bool ->
    FStar_InteractiveHelpers_Base.genv ->
      FStar_Reflection_Types.term ->
        ((FStar_InteractiveHelpers_Base.genv * FStar_Reflection_Types.bv
           FStar_Pervasives_Native.option),
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun dbg ->
    fun ge ->
      fun child ->
        FStar_Tactics_Effect.tac_bind
          (Prims.mk_range "FStar.InteractiveHelpers.Effectful.fst"
             (Prims.of_int (642)) (Prims.of_int (8)) (Prims.of_int (642))
             (Prims.of_int (21)))
          (Prims.mk_range "FStar.InteractiveHelpers.Effectful.fst"
             (Prims.of_int (642)) (Prims.of_int (2)) (Prims.of_int (649))
             (Prims.of_int (17)))
          (Obj.magic (FStar_Tactics_Builtins.inspect child))
          (fun uu___ ->
             (fun uu___ ->
                match uu___ with
                | FStar_Reflection_Data.Tv_Let (recf, attrs, bv, def, body)
                    ->
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_Effect.tac_bind
                            (Prims.mk_range
                               "FStar.InteractiveHelpers.Effectful.fst"
                               (Prims.of_int (644)) (Prims.of_int (7))
                               (Prims.of_int (644)) (Prims.of_int (24)))
                            (Prims.mk_range
                               "FStar.InteractiveHelpers.Effectful.fst"
                               (Prims.of_int (644)) (Prims.of_int (4))
                               (Prims.of_int (648)) (Prims.of_int (39)))
                            (Obj.magic (is_st_get dbg def))
                            (fun uu___1 ->
                               (fun uu___1 ->
                                  if uu___1
                                  then
                                    Obj.magic
                                      (Obj.repr
                                         (FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___2 ->
                                               (ge,
                                                 (FStar_Pervasives_Native.Some
                                                    bv)))))
                                  else
                                    Obj.magic
                                      (Obj.repr
                                         (FStar_Tactics_Effect.tac_bind
                                            (Prims.mk_range
                                               "FStar.InteractiveHelpers.Effectful.fst"
                                               (Prims.of_int (645))
                                               (Prims.of_int (12))
                                               (Prims.of_int (645))
                                               (Prims.of_int (64)))
                                            (Prims.mk_range
                                               "FStar.InteractiveHelpers.Effectful.fst"
                                               (Prims.of_int (645))
                                               (Prims.of_int (9))
                                               (Prims.of_int (648))
                                               (Prims.of_int (39)))
                                            (Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (Prims.mk_range
                                                     "FStar.InteractiveHelpers.Effectful.fst"
                                                     (Prims.of_int (645))
                                                     (Prims.of_int (12))
                                                     (Prims.of_int (645))
                                                     (Prims.of_int (50)))
                                                  (Prims.mk_range
                                                     "FStar.InteractiveHelpers.Effectful.fst"
                                                     (Prims.of_int (645))
                                                     (Prims.of_int (12))
                                                     (Prims.of_int (645))
                                                     (Prims.of_int (64)))
                                                  (Obj.magic
                                                     (term_has_effectful_comp
                                                        dbg
                                                        ge.FStar_InteractiveHelpers_Base.env
                                                        def))
                                                  (fun uu___3 ->
                                                     FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___4 ->
                                                          uu___3 <>
                                                            (FStar_Pervasives_Native.Some
                                                               false)))))
                                            (fun uu___3 ->
                                               (fun uu___3 ->
                                                  if uu___3
                                                  then
                                                    Obj.magic
                                                      (Obj.repr
                                                         (FStar_Tactics_Effect.lift_div_tac
                                                            (fun uu___4 ->
                                                               (ge,
                                                                 FStar_Pervasives_Native.None))))
                                                  else
                                                    Obj.magic
                                                      (Obj.repr
                                                         (FStar_Tactics_Effect.tac_bind
                                                            (Prims.mk_range
                                                               "FStar.InteractiveHelpers.Effectful.fst"
                                                               (Prims.of_int (647))
                                                               (Prims.of_int (16))
                                                               (Prims.of_int (647))
                                                               (Prims.of_int (45)))
                                                            (Prims.mk_range
                                                               "FStar.InteractiveHelpers.Effectful.fst"
                                                               (Prims.of_int (648))
                                                               (Prims.of_int (6))
                                                               (Prims.of_int (648))
                                                               (Prims.of_int (39)))
                                                            (Obj.magic
                                                               (FStar_InteractiveHelpers_Base.genv_push_bv
                                                                  ge bv false
                                                                  FStar_Pervasives_Native.None))
                                                            (fun uu___5 ->
                                                               (fun ge1 ->
                                                                  Obj.magic
                                                                    (
                                                                    find_mem_in_children
                                                                    dbg ge1
                                                                    body))
                                                                 uu___5))))
                                                 uu___3)))) uu___1)))
                | uu___1 ->
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___2 -> (ge, FStar_Pervasives_Native.None)))))
               uu___)
let (pre_post_to_propositions :
  Prims.bool ->
    FStar_InteractiveHelpers_Base.genv ->
      FStar_InteractiveHelpers_ExploreTerm.effect_type ->
        FStar_Reflection_Types.term ->
          FStar_Reflection_Types.binder FStar_Pervasives_Native.option ->
            FStar_InteractiveHelpers_ExploreTerm.type_info ->
              FStar_Reflection_Types.term FStar_Pervasives_Native.option ->
                FStar_Reflection_Types.term FStar_Pervasives_Native.option ->
                  FStar_Reflection_Data.term_view Prims.list ->
                    FStar_Reflection_Data.term_view Prims.list ->
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
                      FStar_Tactics_Effect.tac_bind
                        (Prims.mk_range
                           "FStar.InteractiveHelpers.Effectful.fst"
                           (Prims.of_int (667)) (Prims.of_int (2))
                           (Prims.of_int (667)) (Prims.of_int (52)))
                        (Prims.mk_range
                           "FStar.InteractiveHelpers.Effectful.fst"
                           (Prims.of_int (668)) (Prims.of_int (2))
                           (Prims.of_int (745)) (Prims.of_int (26)))
                        (Obj.magic
                           (FStar_InteractiveHelpers_Base.print_dbg dbg
                              "[> pre_post_to_propositions: begin"))
                        (fun uu___ ->
                           (fun uu___ ->
                              Obj.magic
                                (FStar_Tactics_Effect.tac_bind
                                   (Prims.mk_range
                                      "FStar.InteractiveHelpers.Effectful.fst"
                                      (Prims.of_int (668)) (Prims.of_int (2))
                                      (Prims.of_int (668))
                                      (Prims.of_int (84)))
                                   (Prims.mk_range
                                      "FStar.InteractiveHelpers.Effectful.fst"
                                      (Prims.of_int (669)) (Prims.of_int (2))
                                      (Prims.of_int (745))
                                      (Prims.of_int (26)))
                                   (Obj.magic
                                      (FStar_Tactics_Effect.tac_bind
                                         (Prims.mk_range
                                            "FStar.InteractiveHelpers.Effectful.fst"
                                            (Prims.of_int (668))
                                            (Prims.of_int (16))
                                            (Prims.of_int (668))
                                            (Prims.of_int (84)))
                                         (Prims.mk_range
                                            "FStar.InteractiveHelpers.Effectful.fst"
                                            (Prims.of_int (668))
                                            (Prims.of_int (2))
                                            (Prims.of_int (668))
                                            (Prims.of_int (84)))
                                         (Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (Prims.mk_range
                                                  "FStar.InteractiveHelpers.Effectful.fst"
                                                  (Prims.of_int (668))
                                                  (Prims.of_int (44))
                                                  (Prims.of_int (668))
                                                  (Prims.of_int (83)))
                                               (Prims.mk_range "prims.fst"
                                                  (Prims.of_int (606))
                                                  (Prims.of_int (19))
                                                  (Prims.of_int (606))
                                                  (Prims.of_int (31)))
                                               (Obj.magic
                                                  (FStar_InteractiveHelpers_Base.option_to_string
                                                     FStar_Tactics_Builtins.term_to_string
                                                     opt_pre))
                                               (fun uu___1 ->
                                                  FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___2 ->
                                                       Prims.strcat
                                                         "- uninstantiated pre: "
                                                         uu___1))))
                                         (fun uu___1 ->
                                            (fun uu___1 ->
                                               Obj.magic
                                                 (FStar_InteractiveHelpers_Base.print_dbg
                                                    dbg uu___1)) uu___1)))
                                   (fun uu___1 ->
                                      (fun uu___1 ->
                                         Obj.magic
                                           (FStar_Tactics_Effect.tac_bind
                                              (Prims.mk_range
                                                 "FStar.InteractiveHelpers.Effectful.fst"
                                                 (Prims.of_int (669))
                                                 (Prims.of_int (2))
                                                 (Prims.of_int (669))
                                                 (Prims.of_int (86)))
                                              (Prims.mk_range
                                                 "FStar.InteractiveHelpers.Effectful.fst"
                                                 (Prims.of_int (670))
                                                 (Prims.of_int (2))
                                                 (Prims.of_int (745))
                                                 (Prims.of_int (26)))
                                              (Obj.magic
                                                 (FStar_Tactics_Effect.tac_bind
                                                    (Prims.mk_range
                                                       "FStar.InteractiveHelpers.Effectful.fst"
                                                       (Prims.of_int (669))
                                                       (Prims.of_int (16))
                                                       (Prims.of_int (669))
                                                       (Prims.of_int (86)))
                                                    (Prims.mk_range
                                                       "FStar.InteractiveHelpers.Effectful.fst"
                                                       (Prims.of_int (669))
                                                       (Prims.of_int (2))
                                                       (Prims.of_int (669))
                                                       (Prims.of_int (86)))
                                                    (Obj.magic
                                                       (FStar_Tactics_Effect.tac_bind
                                                          (Prims.mk_range
                                                             "FStar.InteractiveHelpers.Effectful.fst"
                                                             (Prims.of_int (669))
                                                             (Prims.of_int (45))
                                                             (Prims.of_int (669))
                                                             (Prims.of_int (85)))
                                                          (Prims.mk_range
                                                             "prims.fst"
                                                             (Prims.of_int (606))
                                                             (Prims.of_int (19))
                                                             (Prims.of_int (606))
                                                             (Prims.of_int (31)))
                                                          (Obj.magic
                                                             (FStar_InteractiveHelpers_Base.option_to_string
                                                                FStar_Tactics_Builtins.term_to_string
                                                                opt_post))
                                                          (fun uu___2 ->
                                                             FStar_Tactics_Effect.lift_div_tac
                                                               (fun uu___3 ->
                                                                  Prims.strcat
                                                                    "- uninstantiated post: "
                                                                    uu___2))))
                                                    (fun uu___2 ->
                                                       (fun uu___2 ->
                                                          Obj.magic
                                                            (FStar_InteractiveHelpers_Base.print_dbg
                                                               dbg uu___2))
                                                         uu___2)))
                                              (fun uu___2 ->
                                                 (fun uu___2 ->
                                                    Obj.magic
                                                      (FStar_Tactics_Effect.tac_bind
                                                         (Prims.mk_range
                                                            "FStar.InteractiveHelpers.Effectful.fst"
                                                            (Prims.of_int (670))
                                                            (Prims.of_int (12))
                                                            (Prims.of_int (670))
                                                            (Prims.of_int (66)))
                                                         (Prims.mk_range
                                                            "FStar.InteractiveHelpers.Effectful.fst"
                                                            (Prims.of_int (672))
                                                            (Prims.of_int (2))
                                                            (Prims.of_int (745))
                                                            (Prims.of_int (26)))
                                                         (FStar_Tactics_Effect.lift_div_tac
                                                            (fun uu___3 ->
                                                               match ret_abs_binder
                                                               with
                                                               | FStar_Pervasives_Native.None
                                                                   -> []
                                                               | FStar_Pervasives_Native.Some
                                                                   b -> 
                                                                   [b]))
                                                         (fun uu___3 ->
                                                            (fun brs ->
                                                               Obj.magic
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (673))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (727))
                                                                    (Prims.of_int (9)))
                                                                    (
                                                                    Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (672))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (745))
                                                                    (Prims.of_int (26)))
                                                                    (
                                                                    match etype
                                                                    with
                                                                    | 
                                                                    FStar_InteractiveHelpers_ExploreTerm.E_Lemma
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (675))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (675))
                                                                    (Prims.of_int (29)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (676))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (676))
                                                                    (Prims.of_int (34)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    "E_Lemma"))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    (ge0,
                                                                    ([], []),
                                                                    ([
                                                                    FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_Const
                                                                    FStar_Reflection_Data.C_Unit)],
                                                                    [])))))
                                                                    | 
                                                                    FStar_InteractiveHelpers_ExploreTerm.E_Total
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (678))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (678))
                                                                    (Prims.of_int (38)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (679))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (679))
                                                                    (Prims.of_int (29)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    "E_Total/E_GTotal"))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    (ge0,
                                                                    ([], []),
                                                                    ([], [])))))
                                                                    | 
                                                                    FStar_InteractiveHelpers_ExploreTerm.E_GTotal
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (678))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (678))
                                                                    (Prims.of_int (38)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (679))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (679))
                                                                    (Prims.of_int (29)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    "E_Total/E_GTotal"))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    (ge0,
                                                                    ([], []),
                                                                    ([], [])))))
                                                                    | 
                                                                    FStar_InteractiveHelpers_ExploreTerm.E_PURE
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (681))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (681))
                                                                    (Prims.of_int (35)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (682))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (682))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    "E_PURE/E_Pure"))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    (ge0,
                                                                    ([], []),
                                                                    ([v],
                                                                    brs)))))
                                                                    | 
                                                                    FStar_InteractiveHelpers_ExploreTerm.E_Pure
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (681))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (681))
                                                                    (Prims.of_int (35)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (682))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (682))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    "E_PURE/E_Pure"))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    (ge0,
                                                                    ([], []),
                                                                    ([v],
                                                                    brs)))))
                                                                    | 
                                                                    FStar_InteractiveHelpers_ExploreTerm.E_Stack
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (684))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (684))
                                                                    (Prims.of_int (34)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (686))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (698))
                                                                    (Prims.of_int (76)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    "E_Stack/E_ST"))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (686))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (686))
                                                                    (Prims.of_int (66)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (687))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (698))
                                                                    (Prims.of_int (76)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    "Looking for the initial state in the context"))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (687))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (687))
                                                                    (Prims.of_int (54)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (688))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (698))
                                                                    (Prims.of_int (76)))
                                                                    (Obj.magic
                                                                    (find_mem_in_related
                                                                    dbg ge0
                                                                    parents))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    b1_opt ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (688))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (688))
                                                                    (Prims.of_int (64)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (689))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (698))
                                                                    (Prims.of_int (76)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    "Looking for the final state in the context"))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (689))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (689))
                                                                    (Prims.of_int (55)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (691))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (698))
                                                                    (Prims.of_int (76)))
                                                                    (Obj.magic
                                                                    (find_mem_in_related
                                                                    dbg ge0
                                                                    children))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    b2_opt ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (692))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (694))
                                                                    (Prims.of_int (59)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (696))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (698))
                                                                    (Prims.of_int (76)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    fun
                                                                    opt_bv ->
                                                                    fun
                                                                    basename
                                                                    ->
                                                                    fun ge ->
                                                                    match opt_bv
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    bv ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (693))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (693))
                                                                    (Prims.of_int (37)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (693))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (693))
                                                                    (Prims.of_int (55)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Builtins.pack
                                                                    (FStar_Reflection_Data.Tv_Var
                                                                    bv)))
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    (uu___7,
                                                                    (FStar_Reflection_Derived.mk_binder
                                                                    bv), ge)))
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_InteractiveHelpers_Base.genv_push_fresh_var
                                                                    ge
                                                                    basename
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Monotonic";
                                                                    "HyperStack";
                                                                    "mem"])))))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    opt_push_fresh_state
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (696))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (696))
                                                                    (Prims.of_int (63)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (696))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (698))
                                                                    (Prims.of_int (76)))
                                                                    (Obj.magic
                                                                    (opt_push_fresh_state
                                                                    b1_opt
                                                                    "__h0_"
                                                                    ge0))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    match uu___6
                                                                    with
                                                                    | 
                                                                    (h1, b1,
                                                                    ge1) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (697))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (697))
                                                                    (Prims.of_int (63)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (697))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (698))
                                                                    (Prims.of_int (76)))
                                                                    (Obj.magic
                                                                    (opt_push_fresh_state
                                                                    b2_opt
                                                                    "__h1_"
                                                                    ge1))
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    match uu___7
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
                                                                    uu___6)))
                                                                    uu___6)))
                                                                    uu___6)))
                                                                    uu___5)))
                                                                    uu___5)))
                                                                    uu___4)))
                                                                    uu___3))
                                                                    | 
                                                                    FStar_InteractiveHelpers_ExploreTerm.E_ST
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (684))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (684))
                                                                    (Prims.of_int (34)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (686))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (698))
                                                                    (Prims.of_int (76)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    "E_Stack/E_ST"))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (686))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (686))
                                                                    (Prims.of_int (66)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (687))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (698))
                                                                    (Prims.of_int (76)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    "Looking for the initial state in the context"))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (687))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (687))
                                                                    (Prims.of_int (54)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (688))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (698))
                                                                    (Prims.of_int (76)))
                                                                    (Obj.magic
                                                                    (find_mem_in_related
                                                                    dbg ge0
                                                                    parents))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    b1_opt ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (688))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (688))
                                                                    (Prims.of_int (64)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (689))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (698))
                                                                    (Prims.of_int (76)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    "Looking for the final state in the context"))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (689))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (689))
                                                                    (Prims.of_int (55)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (691))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (698))
                                                                    (Prims.of_int (76)))
                                                                    (Obj.magic
                                                                    (find_mem_in_related
                                                                    dbg ge0
                                                                    children))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    b2_opt ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (692))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (694))
                                                                    (Prims.of_int (59)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (696))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (698))
                                                                    (Prims.of_int (76)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    fun
                                                                    opt_bv ->
                                                                    fun
                                                                    basename
                                                                    ->
                                                                    fun ge ->
                                                                    match opt_bv
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    bv ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (693))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (693))
                                                                    (Prims.of_int (37)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (693))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (693))
                                                                    (Prims.of_int (55)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Builtins.pack
                                                                    (FStar_Reflection_Data.Tv_Var
                                                                    bv)))
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    (uu___7,
                                                                    (FStar_Reflection_Derived.mk_binder
                                                                    bv), ge)))
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_InteractiveHelpers_Base.genv_push_fresh_var
                                                                    ge
                                                                    basename
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Monotonic";
                                                                    "HyperStack";
                                                                    "mem"])))))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    opt_push_fresh_state
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (696))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (696))
                                                                    (Prims.of_int (63)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (696))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (698))
                                                                    (Prims.of_int (76)))
                                                                    (Obj.magic
                                                                    (opt_push_fresh_state
                                                                    b1_opt
                                                                    "__h0_"
                                                                    ge0))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    match uu___6
                                                                    with
                                                                    | 
                                                                    (h1, b1,
                                                                    ge1) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (697))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (697))
                                                                    (Prims.of_int (63)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (697))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (698))
                                                                    (Prims.of_int (76)))
                                                                    (Obj.magic
                                                                    (opt_push_fresh_state
                                                                    b2_opt
                                                                    "__h1_"
                                                                    ge1))
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    match uu___7
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
                                                                    uu___6)))
                                                                    uu___6)))
                                                                    uu___6)))
                                                                    uu___5)))
                                                                    uu___5)))
                                                                    uu___4)))
                                                                    uu___3))
                                                                    | 
                                                                    FStar_InteractiveHelpers_ExploreTerm.E_Unknown
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (706))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (706))
                                                                    (Prims.of_int (84)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (707))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (726))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (check_opt_pre_post_type
                                                                    dbg
                                                                    ge0.FStar_InteractiveHelpers_Base.env
                                                                    opt_pre
                                                                    ret_type.FStar_InteractiveHelpers_ExploreTerm.ty
                                                                    opt_post))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    pp_type
                                                                    ->
                                                                    match pp_type
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (PP_Pure)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (709))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (709))
                                                                    (Prims.of_int (31)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (711))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (711))
                                                                    (Prims.of_int (33)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    "PP_Pure"))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    (ge0,
                                                                    ([], []),
                                                                    ([v],
                                                                    brs)))))
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (PP_State
                                                                    state_type)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (713))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (713))
                                                                    (Prims.of_int (32)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (715))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (716))
                                                                    (Prims.of_int (78)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    "PP_State"))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (715))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (715))
                                                                    (Prims.of_int (79)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (715))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (716))
                                                                    (Prims.of_int (78)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.genv_push_two_fresh_vars
                                                                    ge0 "__s"
                                                                    state_type))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    match uu___4
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
                                                                    uu___3))
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (PP_Unknown)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (718))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (718))
                                                                    (Prims.of_int (34)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (720))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (722))
                                                                    (Prims.of_int (67)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    "PP_Unknown"))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (720))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (720))
                                                                    (Prims.of_int (86)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (720))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (722))
                                                                    (Prims.of_int (67)))
                                                                    (Obj.magic
                                                                    (introduce_variables_for_opt_abs
                                                                    ge0
                                                                    opt_pre))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    (pre_values,
                                                                    pre_binders,
                                                                    ge1) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (721))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (721))
                                                                    (Prims.of_int (89)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (721))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (722))
                                                                    (Prims.of_int (67)))
                                                                    (Obj.magic
                                                                    (introduce_variables_for_opt_abs
                                                                    ge1
                                                                    opt_post))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    match uu___5
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
                                                                    uu___4)))
                                                                    uu___3))
                                                                    | 
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (724))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (724))
                                                                    (Prims.of_int (42)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (726))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (726))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    "No pre and no post"))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    (ge0,
                                                                    ([], []),
                                                                    ([], []))))))
                                                                    uu___3)))
                                                                    (
                                                                    fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    (ge3,
                                                                    (pre_values,
                                                                    pre_binders),
                                                                    (post_values,
                                                                    post_binders))
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (731))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (731))
                                                                    (Prims.of_int (59)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (736))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (745))
                                                                    (Prims.of_int (26)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.opt_mk_app_norm
                                                                    ge3.FStar_InteractiveHelpers_Base.env
                                                                    opt_pre
                                                                    pre_values))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    pre_prop
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (737))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (741))
                                                                    (Prims.of_int (10)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (744))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (745))
                                                                    (Prims.of_int (26)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Derived.try_with
                                                                    (fun
                                                                    uu___4 ->
                                                                    match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    FStar_InteractiveHelpers_Base.opt_mk_app_norm
                                                                    ge3.FStar_InteractiveHelpers_Base.env
                                                                    opt_post
                                                                    post_values)
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (740))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (740))
                                                                    (Prims.of_int (75)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (741))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (741))
                                                                    (Prims.of_int (10)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    "Dropping a postcondition because of incoherent typing"))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Pervasives_Native.None)))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    post_prop
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (744))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (744))
                                                                    (Prims.of_int (50)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (745))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (745))
                                                                    (Prims.of_int (26)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    "[> pre_post_to_propositions: end"))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    (ge3,
                                                                    pre_prop,
                                                                    post_prop)))))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___3)))
                                                              uu___3)))
                                                   uu___2))) uu___1))) uu___)
let (eterm_info_to_assertions :
  Prims.bool ->
    Prims.bool ->
      Prims.bool ->
        FStar_InteractiveHelpers_Base.genv ->
          FStar_Reflection_Types.term ->
            Prims.bool ->
              Prims.bool ->
                eterm_info ->
                  FStar_Reflection_Types.term FStar_Pervasives_Native.option
                    ->
                    FStar_InteractiveHelpers_ExploreTerm.typ_or_comp
                      FStar_Pervasives_Native.option ->
                      FStar_Reflection_Data.term_view Prims.list ->
                        FStar_Reflection_Data.term_view Prims.list ->
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
                          FStar_Tactics_Effect.tac_bind
                            (Prims.mk_range
                               "FStar.InteractiveHelpers.Effectful.fst"
                               (Prims.of_int (769)) (Prims.of_int (2))
                               (Prims.of_int (769)) (Prims.of_int (45)))
                            (Prims.mk_range
                               "FStar.InteractiveHelpers.Effectful.fst"
                               (Prims.of_int (774)) (Prims.of_int (2))
                               (Prims.of_int (965)) (Prims.of_int (7)))
                            (Obj.magic
                               (FStar_InteractiveHelpers_Base.print_dbg dbg
                                  "[> eterm_info_to_assertions"))
                            (fun uu___ ->
                               (fun uu___ ->
                                  Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (Prims.mk_range
                                          "FStar.InteractiveHelpers.Effectful.fst"
                                          (Prims.of_int (774))
                                          (Prims.of_int (14))
                                          (Prims.of_int (774))
                                          (Prims.of_int (24)))
                                       (Prims.mk_range
                                          "FStar.InteractiveHelpers.Effectful.fst"
                                          (Prims.of_int (775))
                                          (Prims.of_int (2))
                                          (Prims.of_int (965))
                                          (Prims.of_int (7)))
                                       (FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___1 -> info.einfo))
                                       (fun uu___1 ->
                                          (fun einfo ->
                                             Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (Prims.mk_range
                                                     "FStar.InteractiveHelpers.Effectful.fst"
                                                     (Prims.of_int (776))
                                                     (Prims.of_int (4))
                                                     (Prims.of_int (792))
                                                     (Prims.of_int (22)))
                                                  (Prims.mk_range
                                                     "FStar.InteractiveHelpers.Effectful.fst"
                                                     (Prims.of_int (775))
                                                     (Prims.of_int (2))
                                                     (Prims.of_int (965))
                                                     (Prims.of_int (7)))
                                                  (match bind_var with
                                                   | FStar_Pervasives_Native.Some
                                                       v ->
                                                       Obj.magic
                                                         (Obj.repr
                                                            (FStar_Tactics_Effect.lift_div_tac
                                                               (fun uu___1 ->
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
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (785))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (785))
                                                                    (Prims.of_int (44)))
                                                                    (
                                                                    Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (785))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (791))
                                                                    (Prims.of_int (53)))
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_InteractiveHelpers_ExploreTerm.is_unit_type
                                                                    (einfo.ei_ret_type).FStar_InteractiveHelpers_ExploreTerm.ty))
                                                                    (
                                                                    fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    uu___1 ->
                                                                    if uu___1
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    (ge,
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_Const
                                                                    FStar_Reflection_Data.C_Unit)),
                                                                    FStar_Pervasives_Native.None))))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (788))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (788))
                                                                    (Prims.of_int (66)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (789))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (791))
                                                                    (Prims.of_int (53)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.fresh_binder
                                                                    ge.FStar_InteractiveHelpers_Base.env
                                                                    "__ret"
                                                                    (einfo.ei_ret_type).FStar_InteractiveHelpers_ExploreTerm.ty))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun b ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (789))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (789))
                                                                    (Prims.of_int (33)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (790))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (791))
                                                                    (Prims.of_int (53)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Reflection_Derived.bv_of_binder
                                                                    b))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun bv
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (790))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (790))
                                                                    (Prims.of_int (35)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (791))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (791))
                                                                    (Prims.of_int (53)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Builtins.pack
                                                                    (FStar_Reflection_Data.Tv_Var
                                                                    bv)))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun tm
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (791))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (791))
                                                                    (Prims.of_int (41)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (791))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (791))
                                                                    (Prims.of_int (53)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.genv_push_binder
                                                                    ge b true
                                                                    FStar_Pervasives_Native.None))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    (uu___3,
                                                                    tm,
                                                                    (FStar_Pervasives_Native.Some
                                                                    b))))))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___3))))
                                                                    uu___1))
                                                             else
                                                               Obj.repr
                                                                 (FStar_Tactics_Effect.lift_div_tac
                                                                    (
                                                                    fun
                                                                    uu___2 ->
                                                                    (ge, t,
                                                                    FStar_Pervasives_Native.None))))))
                                                  (fun uu___1 ->
                                                     (fun uu___1 ->
                                                        match uu___1 with
                                                        | (ge0, v, opt_b) ->
                                                            Obj.magic
                                                              (FStar_Tactics_Effect.tac_bind
                                                                 (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (795))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (965))
                                                                    (Prims.of_int (7)))
                                                                 (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (795))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (965))
                                                                    (Prims.of_int (7)))
                                                                 (FStar_Tactics_Effect.lift_div_tac
                                                                    (
                                                                    fun
                                                                    uu___2 ->
                                                                    v))
                                                                 (fun uu___2
                                                                    ->
                                                                    (fun v1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (795))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (795))
                                                                    (Prims.of_int (53)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (796))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (965))
                                                                    (Prims.of_int (7)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    "> Instantiating local pre/post"))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (797))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (798))
                                                                    (Prims.of_int (72)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (796))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (965))
                                                                    (Prims.of_int (7)))
                                                                    (Obj.magic
                                                                    (pre_post_to_propositions
                                                                    dbg ge0
                                                                    einfo.ei_type
                                                                    v1 opt_b
                                                                    einfo.ei_ret_type
                                                                    einfo.ei_pre
                                                                    einfo.ei_post
                                                                    parents
                                                                    children))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    (ge1,
                                                                    pre_prop,
                                                                    post_prop)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (799))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (799))
                                                                    (Prims.of_int (75)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (800))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (965))
                                                                    (Prims.of_int (7)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (799))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (799))
                                                                    (Prims.of_int (75)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (799))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (799))
                                                                    (Prims.of_int (75)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (799))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (799))
                                                                    (Prims.of_int (74)))
                                                                    (Prims.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.option_to_string
                                                                    FStar_Tactics_Builtins.term_to_string
                                                                    pre_prop))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Prims.strcat
                                                                    "- pre prop: "
                                                                    uu___4))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    uu___4))
                                                                    uu___4)))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (800))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (800))
                                                                    (Prims.of_int (77)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (804))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (965))
                                                                    (Prims.of_int (7)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (800))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (800))
                                                                    (Prims.of_int (77)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (800))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (800))
                                                                    (Prims.of_int (77)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (800))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (800))
                                                                    (Prims.of_int (76)))
                                                                    (Prims.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.option_to_string
                                                                    FStar_Tactics_Builtins.term_to_string
                                                                    post_prop))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Prims.strcat
                                                                    "- post prop: "
                                                                    uu___5))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    uu___5))
                                                                    uu___5)))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    if
                                                                    is_assert
                                                                    then
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (806))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (806))
                                                                    (Prims.of_int (70)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (807))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (807))
                                                                    (Prims.of_int (53)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    "The term is an assert: only keep the postcondition"))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
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
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (815))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (938))
                                                                    (Prims.of_int (18)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (811))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (964))
                                                                    (Prims.of_int (39)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (815))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (815))
                                                                    (Prims.of_int (70)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (816))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (937))
                                                                    (Prims.of_int (31)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    with_gpre
                                                                    ||
                                                                    ((Prims.op_Negation
                                                                    is_let)
                                                                    &&
                                                                    with_gpost)))
                                                                    (fun
                                                                    uu___7 ->
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
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (818))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (818))
                                                                    (Prims.of_int (53)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (819))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (935))
                                                                    (Prims.of_int (62)))
                                                                    (Obj.magic
                                                                    (typ_or_comp_to_effect_info
                                                                    dbg ge1 c))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun ei
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (819))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (819))
                                                                    (Prims.of_int (70)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (820))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (935))
                                                                    (Prims.of_int (62)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (819))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (819))
                                                                    (Prims.of_int (70)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (819))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (819))
                                                                    (Prims.of_int (70)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (819))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (819))
                                                                    (Prims.of_int (69)))
                                                                    (Prims.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (effect_info_to_string
                                                                    ei))
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    Prims.strcat
                                                                    "- target effect: "
                                                                    uu___7))))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    uu___7))
                                                                    uu___7)))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (820))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (820))
                                                                    (Prims.of_int (92)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (821))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (935))
                                                                    (Prims.of_int (62)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (820))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (820))
                                                                    (Prims.of_int (92)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (820))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (820))
                                                                    (Prims.of_int (92)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (820))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (820))
                                                                    (Prims.of_int (91)))
                                                                    (Prims.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.option_to_string
                                                                    FStar_Tactics_Builtins.term_to_string
                                                                    ei.ei_pre))
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    Prims.strcat
                                                                    "- global unfilt. pre: "
                                                                    uu___8))))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    uu___8))
                                                                    uu___8)))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (821))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (821))
                                                                    (Prims.of_int (94)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (824))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (935))
                                                                    (Prims.of_int (62)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (821))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (821))
                                                                    (Prims.of_int (94)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (821))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (821))
                                                                    (Prims.of_int (94)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (821))
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (821))
                                                                    (Prims.of_int (93)))
                                                                    (Prims.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.option_to_string
                                                                    FStar_Tactics_Builtins.term_to_string
                                                                    ei.ei_post))
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    Prims.strcat
                                                                    "- global unfilt. post: "
                                                                    uu___9))))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    uu___9))
                                                                    uu___9)))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (825))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (867))
                                                                    (Prims.of_int (32)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (872))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (935))
                                                                    (Prims.of_int (62)))
                                                                    (if
                                                                    with_gpre
                                                                    then
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (828))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (828))
                                                                    (Prims.of_int (83)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (829))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (860))
                                                                    (Prims.of_int (34)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    "Generating assertions from the global parameters' types"))
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (829))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (829))
                                                                    (Prims.of_int (66)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (833))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (860))
                                                                    (Prims.of_int (34)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (829))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (829))
                                                                    (Prims.of_int (66)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (829))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (829))
                                                                    (Prims.of_int (66)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (829))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (829))
                                                                    (Prims.of_int (65)))
                                                                    (Prims.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.genv_to_string
                                                                    ge1))
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    Prims.strcat
                                                                    "Current genv:\n"
                                                                    uu___11))))
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    uu___11))
                                                                    uu___11)))
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (834))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (834))
                                                                    (Prims.of_int (91)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (835))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (860))
                                                                    (Prims.of_int (34)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_List_Tot_Base.rev
                                                                    (FStar_List_Tot_Base.map
                                                                    (fun x ->
                                                                    (x,
                                                                    (FStar_Reflection_Derived.type_of_binder
                                                                    x)))
                                                                    (FStar_InteractiveHelpers_ExploreTerm.params_of_typ_or_comp
                                                                    c))))
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    params ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (835))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (836))
                                                                    (Prims.of_int (74)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (838))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (860))
                                                                    (Prims.of_int (34)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Util.iteri
                                                                    (fun i ->
                                                                    fun
                                                                    uu___12
                                                                    ->
                                                                    match uu___12
                                                                    with
                                                                    | 
                                                                    (b,
                                                                    uu___13)
                                                                    ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (835))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (836))
                                                                    (Prims.of_int (66)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (835))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (836))
                                                                    (Prims.of_int (66)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (835))
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (836))
                                                                    (Prims.of_int (65)))
                                                                    (Prims.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (836))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (836))
                                                                    (Prims.of_int (65)))
                                                                    (Prims.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (836))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (836))
                                                                    (Prims.of_int (65)))
                                                                    (Prims.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Derived.binder_to_string
                                                                    b))
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    Prims.strcat
                                                                    ": "
                                                                    uu___14))))
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    Prims.strcat
                                                                    (Prims.string_of_int
                                                                    i)
                                                                    uu___14))))
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    Prims.strcat
                                                                    "Global parameter "
                                                                    uu___14))))
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
                                                                    uu___14))
                                                                    params))
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (838))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (838))
                                                                    (Prims.of_int (84)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (840))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (860))
                                                                    (Prims.of_int (34)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Util.filter
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    match uu___13
                                                                    with
                                                                    | 
                                                                    (b,
                                                                    uu___15)
                                                                    ->
                                                                    Prims.op_Negation
                                                                    (FStar_InteractiveHelpers_Base.binder_is_shadowed
                                                                    ge1 b))))
                                                                    uu___13)
                                                                    params))
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (fun
                                                                    params1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (841))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (857))
                                                                    (Prims.of_int (22)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (859))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (860))
                                                                    (Prims.of_int (34)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    fun x ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (841))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (841))
                                                                    (Prims.of_int (27)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (841))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (857))
                                                                    (Prims.of_int (22)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___14
                                                                    -> x))
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    match uu___14
                                                                    with
                                                                    | 
                                                                    (b, ty)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (842))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (842))
                                                                    (Prims.of_int (37)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (843))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (857))
                                                                    (Prims.of_int (22)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    FStar_Reflection_Derived.bv_of_binder
                                                                    b))
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    (fun bv
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (843))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (843))
                                                                    (Prims.of_int (98)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (844))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (857))
                                                                    (Prims.of_int (22)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (843))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (843))
                                                                    (Prims.of_int (98)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (843))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (843))
                                                                    (Prims.of_int (98)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (843))
                                                                    (Prims.of_int (79))
                                                                    (Prims.of_int (843))
                                                                    (Prims.of_int (97)))
                                                                    (Prims.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Derived.binder_to_string
                                                                    b))
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    Prims.strcat
                                                                    "Generating assertions from global parameter: "
                                                                    uu___15))))
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    uu___15))
                                                                    uu___15)))
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (844))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (844))
                                                                    (Prims.of_int (52)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (845))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (857))
                                                                    (Prims.of_int (22)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_ExploreTerm.get_type_info_from_type
                                                                    ty))
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    (fun
                                                                    tinfo ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (845))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (845))
                                                                    (Prims.of_int (38)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (846))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (857))
                                                                    (Prims.of_int (22)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Builtins.pack
                                                                    (FStar_Reflection_Data.Tv_Var
                                                                    bv)))
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    (fun v2
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (846))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (846))
                                                                    (Prims.of_int (45)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (847))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (857))
                                                                    (Prims.of_int (22)))
                                                                    (Obj.magic
                                                                    (mk_has_type
                                                                    v2
                                                                    tinfo.FStar_InteractiveHelpers_ExploreTerm.ty))
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    (fun p1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (847))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (855))
                                                                    (Prims.of_int (76)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (857))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (857))
                                                                    (Prims.of_int (19)))
                                                                    (match 
                                                                    tinfo.FStar_InteractiveHelpers_ExploreTerm.refin
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___16
                                                                    -> [])))
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    r ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (850))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (850))
                                                                    (Prims.of_int (50)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (853))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (855))
                                                                    (Prims.of_int (76)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.mk_app_norm
                                                                    ge1.FStar_InteractiveHelpers_Base.env
                                                                    r [v2]))
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    (fun p2
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (853))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (853))
                                                                    (Prims.of_int (53)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (853))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (855))
                                                                    (Prims.of_int (76)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_ExploreTerm.term_has_shadowed_variables
                                                                    ge1 p2))
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    if
                                                                    uu___16
                                                                    then
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (854))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (854))
                                                                    (Prims.of_int (99)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (854))
                                                                    (Prims.of_int (101))
                                                                    (Prims.of_int (854))
                                                                    (Prims.of_int (103)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    "Discarding type refinement because of shadowed variables"))
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___18
                                                                    -> [])))
                                                                    else
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (855))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (855))
                                                                    (Prims.of_int (66)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (855))
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (855))
                                                                    (Prims.of_int (72)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    "Keeping type refinement"))
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___19
                                                                    -> [p2]))))
                                                                    uu___16)))
                                                                    uu___16))))
                                                                    (fun pl
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___16
                                                                    -> p1 ::
                                                                    pl))))
                                                                    uu___16)))
                                                                    uu___16)))
                                                                    uu___16)))
                                                                    uu___15)))
                                                                    uu___15)))
                                                                    uu___14)))
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (fun
                                                                    param_to_props
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (859))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (859))
                                                                    (Prims.of_int (49)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (860))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (860))
                                                                    (Prims.of_int (34)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Util.map
                                                                    param_to_props
                                                                    params1))
                                                                    (fun
                                                                    props ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    FStar_List_Tot_Base.flatten
                                                                    props))))
                                                                    uu___13)))
                                                                    uu___13)))
                                                                    uu___12)))
                                                                    uu___12)))
                                                                    uu___11)))
                                                                    uu___10))
                                                                    else
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (864))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (864))
                                                                    (Prims.of_int (65)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (865))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (865))
                                                                    (Prims.of_int (14)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    "Ignoring the global parameters' types"))
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    -> []))))
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    gparams_props
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (873))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (881))
                                                                    (Prims.of_int (21)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (885))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (935))
                                                                    (Prims.of_int (62)))
                                                                    (match 
                                                                    ((ei.ei_pre),
                                                                    with_gpre)
                                                                    with
                                                                    | 
                                                                    (FStar_Pervasives_Native.Some
                                                                    pre,
                                                                    true) ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (875))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (875))
                                                                    (Prims.of_int (50)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (875))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (880))
                                                                    (Prims.of_int (26)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_ExploreTerm.term_has_shadowed_variables
                                                                    ge1 pre))
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    if
                                                                    uu___10
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (877))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (877))
                                                                    (Prims.of_int (92)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (878))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (878))
                                                                    (Prims.of_int (18)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    "Dropping the global precondition because of shadowed variables"))
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_Pervasives_Native.None))))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    ei.ei_pre))))
                                                                    uu___10)))
                                                                    | 
                                                                    uu___10
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Pervasives_Native.None))))
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun gpre
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (886))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (913))
                                                                    (Prims.of_int (22)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (885))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (935))
                                                                    (Prims.of_int (62)))
                                                                    (if
                                                                    Prims.op_Negation
                                                                    with_gpost
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (FStar_Pervasives_Native.None,
                                                                    []))))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (if
                                                                    is_let
                                                                    then
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (889))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (889))
                                                                    (Prims.of_int (118)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (890))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (890))
                                                                    (Prims.of_int (20)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    "Dropping the global postcondition and return type because we are studying a let expression"))
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (FStar_Pervasives_Native.None,
                                                                    [])))
                                                                    else
                                                                    FStar_Tactics_Derived.try_with
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (901))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (901))
                                                                    (Prims.of_int (81)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (902))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (909))
                                                                    (Prims.of_int (50)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    "> Generating propositions from the global type cast"))
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (902))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (902))
                                                                    (Prims.of_int (86)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (903))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (909))
                                                                    (Prims.of_int (50)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (902))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (902))
                                                                    (Prims.of_int (86)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (902))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (902))
                                                                    (Prims.of_int (86)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (902))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (902))
                                                                    (Prims.of_int (85)))
                                                                    (Prims.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_ExploreTerm.type_info_to_string
                                                                    einfo.ei_ret_type))
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    Prims.strcat
                                                                    "- known type: "
                                                                    uu___14))))
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
                                                                    uu___14)))
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (903))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (903))
                                                                    (Prims.of_int (83)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (904))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (909))
                                                                    (Prims.of_int (50)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (903))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (903))
                                                                    (Prims.of_int (83)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (903))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (903))
                                                                    (Prims.of_int (83)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (903))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (903))
                                                                    (Prims.of_int (82)))
                                                                    (Prims.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_ExploreTerm.type_info_to_string
                                                                    ei.ei_ret_type))
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    Prims.strcat
                                                                    "- exp. type : "
                                                                    uu___15))))
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    uu___15))
                                                                    uu___15)))
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (904))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (904))
                                                                    (Prims.of_int (87)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (905))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (909))
                                                                    (Prims.of_int (50)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    mk_cast_info
                                                                    v1
                                                                    (FStar_Pervasives_Native.Some
                                                                    (einfo.ei_ret_type))
                                                                    (FStar_Pervasives_Native.Some
                                                                    (ei.ei_ret_type))))
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    (fun
                                                                    gcast ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (905))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (905))
                                                                    (Prims.of_int (55)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (906))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (909))
                                                                    (Prims.of_int (50)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (905))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (905))
                                                                    (Prims.of_int (55)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (905))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (905))
                                                                    (Prims.of_int (55)))
                                                                    (Obj.magic
                                                                    (cast_info_to_string
                                                                    gcast))
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    uu___16))
                                                                    uu___16)))
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (906))
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (906))
                                                                    (Prims.of_int (71)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (907))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (909))
                                                                    (Prims.of_int (50)))
                                                                    (Obj.magic
                                                                    (cast_info_to_propositions
                                                                    dbg ge1
                                                                    gcast))
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    (fun
                                                                    gcast_props
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (907))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (907))
                                                                    (Prims.of_int (66)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (908))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (909))
                                                                    (Prims.of_int (50)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    "> Propositions for global type cast:"))
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (908))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (908))
                                                                    (Prims.of_int (71)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (909))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (909))
                                                                    (Prims.of_int (50)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (908))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (908))
                                                                    (Prims.of_int (71)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (908))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (908))
                                                                    (Prims.of_int (71)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.list_to_string
                                                                    FStar_Tactics_Builtins.term_to_string
                                                                    gcast_props))
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
                                                                    uu___18)))
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    ((ei.ei_post),
                                                                    (FStar_List_Tot_Base.rev
                                                                    gcast_props))))))
                                                                    uu___17)))
                                                                    uu___17)))
                                                                    uu___16)))
                                                                    uu___16)))
                                                                    uu___15)))
                                                                    uu___14)))
                                                                    uu___13))
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (912))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (912))
                                                                    (Prims.of_int (108)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (913))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (913))
                                                                    (Prims.of_int (22)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    "Dropping the global postcondition and return type because of incoherent typing"))
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    (FStar_Pervasives_Native.None,
                                                                    [])))))))
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    match uu___10
                                                                    with
                                                                    | 
                                                                    (gpost,
                                                                    gcast_props)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (917))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (917))
                                                                    (Prims.of_int (55)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (923))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (935))
                                                                    (Prims.of_int (62)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    "> Instantiating global pre/post"))
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (924))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (926))
                                                                    (Prims.of_int (22)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (928))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (935))
                                                                    (Prims.of_int (62)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
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
                                                                    parents))
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    gchildren
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (929))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (930))
                                                                    (Prims.of_int (69)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (928))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (935))
                                                                    (Prims.of_int (62)))
                                                                    (Obj.magic
                                                                    (pre_post_to_propositions
                                                                    dbg ge1
                                                                    ei.ei_type
                                                                    v1 opt_b
                                                                    einfo.ei_ret_type
                                                                    gpre
                                                                    gpost
                                                                    (FStar_List_Tot_Base.rev
                                                                    parents)
                                                                    gchildren))
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    match uu___12
                                                                    with
                                                                    | 
                                                                    (ge2,
                                                                    gpre_prop,
                                                                    gpost_prop)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (932))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (932))
                                                                    (Prims.of_int (89)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (933))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (935))
                                                                    (Prims.of_int (62)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (932))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (932))
                                                                    (Prims.of_int (89)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (932))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (932))
                                                                    (Prims.of_int (89)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (932))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (932))
                                                                    (Prims.of_int (88)))
                                                                    (Prims.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.option_to_string
                                                                    FStar_Tactics_Builtins.term_to_string
                                                                    gpre_prop))
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    Prims.strcat
                                                                    "- global pre prop: "
                                                                    uu___13))))
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    uu___13))
                                                                    uu___13)))
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (933))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (933))
                                                                    (Prims.of_int (91)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (935))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (935))
                                                                    (Prims.of_int (62)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (933))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (933))
                                                                    (Prims.of_int (91)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (933))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (933))
                                                                    (Prims.of_int (91)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (933))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (933))
                                                                    (Prims.of_int (90)))
                                                                    (Prims.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.option_to_string
                                                                    FStar_Tactics_Builtins.term_to_string
                                                                    gpost_prop))
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    Prims.strcat
                                                                    "- global post prop: "
                                                                    uu___14))))
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
                                                                    uu___14)))
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    (ge2,
                                                                    gparams_props,
                                                                    gpre_prop,
                                                                    gcast_props,
                                                                    gpost_prop)))))
                                                                    uu___13)))
                                                                    uu___12)))
                                                                    uu___12)))
                                                                    uu___11)))
                                                                    uu___10)))
                                                                    uu___10)))
                                                                    uu___10)))
                                                                    uu___9)))
                                                                    uu___8)))
                                                                    uu___7)))
                                                                    uu___7)))
                                                                    | 
                                                                    (uu___7,
                                                                    uu___8)
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    (ge1, [],
                                                                    FStar_Pervasives_Native.None,
                                                                    [],
                                                                    FStar_Pervasives_Native.None)))))
                                                                    uu___7)))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    match uu___7
                                                                    with
                                                                    | 
                                                                    (ge2,
                                                                    gparams_props,
                                                                    gpre_prop,
                                                                    gcast_props,
                                                                    gpost_prop)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (942))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (942))
                                                                    (Prims.of_int (77)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (944))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (964))
                                                                    (Prims.of_int (39)))
                                                                    (Obj.magic
                                                                    (cast_info_list_to_propositions
                                                                    dbg ge2
                                                                    info.parameters))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    params_props
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (945))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (946))
                                                                    (Prims.of_int (63)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (944))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (964))
                                                                    (Prims.of_int (39)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
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
                                                                    -> [])))))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    match uu___8
                                                                    with
                                                                    | 
                                                                    (ret_values,
                                                                    ret_binders)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (947))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (964))
                                                                    (Prims.of_int (39)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (947))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (964))
                                                                    (Prims.of_int (39)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    ret_values))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    ret_values1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (948))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (950))
                                                                    (Prims.of_int (17)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (952))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (964))
                                                                    (Prims.of_int (39)))
                                                                    (match ret_values1
                                                                    with
                                                                    | 
                                                                    v2::[] ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (949))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (949))
                                                                    (Prims.of_int (56)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (949))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (949))
                                                                    (Prims.of_int (56)))
                                                                    (Obj.magic
                                                                    (mk_has_type
                                                                    v2
                                                                    (einfo.ei_ret_type).FStar_InteractiveHelpers_ExploreTerm.ty))
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___9))))
                                                                    | 
                                                                    uu___9 ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Pervasives_Native.None))))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    ret_has_type_prop
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (952))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (952))
                                                                    (Prims.of_int (97)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (954))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (964))
                                                                    (Prims.of_int (39)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.opt_mk_app_norm
                                                                    ge2.FStar_InteractiveHelpers_Base.env
                                                                    (get_opt_refinment
                                                                    einfo.ei_ret_type)
                                                                    ret_values1))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    ret_refin_prop
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (954))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (954))
                                                                    (Prims.of_int (83)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (955))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (964))
                                                                    (Prims.of_int (39)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_InteractiveHelpers_Base.opt_cons
                                                                    gpre_prop
                                                                    (FStar_List_Tot_Base.append
                                                                    params_props
                                                                    (FStar_InteractiveHelpers_Base.opt_cons
                                                                    pre_prop
                                                                    []))))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun pres
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (955))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (955))
                                                                    (Prims.of_int (40)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (956))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (964))
                                                                    (Prims.of_int (39)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_List_Tot_Base.append
                                                                    gparams_props
                                                                    pres))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    pres1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (956))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (958))
                                                                    (Prims.of_int (69)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (960))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (964))
                                                                    (Prims.of_int (39)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
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
                                                                    []))))))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    posts ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (960))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (960))
                                                                    (Prims.of_int (37)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (961))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (964))
                                                                    (Prims.of_int (39)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    "- generated pres:"))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (961))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (961))
                                                                    (Prims.of_int (61)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (962))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (964))
                                                                    (Prims.of_int (39)))
                                                                    (if dbg
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Util.iter
                                                                    (fun x ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (961))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (961))
                                                                    (Prims.of_int (55)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (961))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (961))
                                                                    (Prims.of_int (55)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Builtins.term_to_string
                                                                    x))
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Builtins.print
                                                                    uu___10))
                                                                    uu___10))
                                                                    pres1))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    -> ()))))
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (962))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (962))
                                                                    (Prims.of_int (38)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (963))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (964))
                                                                    (Prims.of_int (39)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    "- generated posts:"))
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (963))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (963))
                                                                    (Prims.of_int (62)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (964))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (964))
                                                                    (Prims.of_int (39)))
                                                                    (if dbg
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Util.iter
                                                                    (fun x ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (963))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (963))
                                                                    (Prims.of_int (55)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.Effectful.fst"
                                                                    (Prims.of_int (963))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (963))
                                                                    (Prims.of_int (55)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Builtins.term_to_string
                                                                    x))
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Builtins.print
                                                                    uu___12))
                                                                    uu___12))
                                                                    posts))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    -> ()))))
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (ge2,
                                                                    {
                                                                    FStar_InteractiveHelpers_Propositions.pres
                                                                    = pres1;
                                                                    FStar_InteractiveHelpers_Propositions.posts
                                                                    = posts
                                                                    })))))
                                                                    uu___11)))
                                                                    uu___10)))
                                                                    uu___9)))
                                                                    uu___9)))
                                                                    uu___9)))
                                                                    uu___9)))
                                                                    uu___9)))
                                                                    uu___9)))
                                                                    uu___9)))
                                                                    uu___8)))
                                                                    uu___8)))
                                                                    uu___7)))
                                                                    uu___5)))
                                                                    uu___4)))
                                                                    uu___3)))
                                                                    uu___2)))
                                                                    uu___2)))
                                                       uu___1))) uu___1)))
                                 uu___)