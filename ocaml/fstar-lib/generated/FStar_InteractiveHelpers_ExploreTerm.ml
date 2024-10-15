open Prims
let (pure_effect_qn : Prims.string) = "Prims.PURE"
let (pure_hoare_effect_qn : Prims.string) = "Prims.Pure"
let (stack_effect_qn : Prims.string) = "FStar.HyperStack.ST.Stack"
let (st_effect_qn : Prims.string) = "FStar.HyperStack.ST.ST"
let (comp_qualifier :
  FStarC_Reflection_Types.comp ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    (fun c ->
       Obj.magic
         (FStar_Tactics_Effect.lift_div_tac
            (fun uu___ ->
               match FStarC_Reflection_V1_Builtins.inspect_comp c with
               | FStarC_Reflection_V1_Data.C_Total uu___1 -> "C_Total"
               | FStarC_Reflection_V1_Data.C_GTotal uu___1 -> "C_GTotal"
               | FStarC_Reflection_V1_Data.C_Lemma (uu___1, uu___2, uu___3)
                   -> "C_Lemma"
               | FStarC_Reflection_V1_Data.C_Eff
                   (uu___1, uu___2, uu___3, uu___4, uu___5) -> "C_Eff")))
      uu___
type effect_type =
  | E_Total 
  | E_GTotal 
  | E_Lemma 
  | E_PURE 
  | E_Pure 
  | E_Stack 
  | E_ST 
  | E_Unknown 
let (uu___is_E_Total : effect_type -> Prims.bool) =
  fun projectee -> match projectee with | E_Total -> true | uu___ -> false
let (uu___is_E_GTotal : effect_type -> Prims.bool) =
  fun projectee -> match projectee with | E_GTotal -> true | uu___ -> false
let (uu___is_E_Lemma : effect_type -> Prims.bool) =
  fun projectee -> match projectee with | E_Lemma -> true | uu___ -> false
let (uu___is_E_PURE : effect_type -> Prims.bool) =
  fun projectee -> match projectee with | E_PURE -> true | uu___ -> false
let (uu___is_E_Pure : effect_type -> Prims.bool) =
  fun projectee -> match projectee with | E_Pure -> true | uu___ -> false
let (uu___is_E_Stack : effect_type -> Prims.bool) =
  fun projectee -> match projectee with | E_Stack -> true | uu___ -> false
let (uu___is_E_ST : effect_type -> Prims.bool) =
  fun projectee -> match projectee with | E_ST -> true | uu___ -> false
let (uu___is_E_Unknown : effect_type -> Prims.bool) =
  fun projectee -> match projectee with | E_Unknown -> true | uu___ -> false
let (effect_type_to_string : effect_type -> Prims.string) =
  fun ety ->
    match ety with
    | E_Total -> "E_Total"
    | E_GTotal -> "E_GTotal"
    | E_Lemma -> "E_Lemma"
    | E_PURE -> "E_PURE"
    | E_Pure -> "E_Pure"
    | E_Stack -> "E_Stack"
    | E_ST -> "E_ST"
    | E_Unknown -> "E_Unknown"
let (effect_name_to_type : FStarC_Reflection_Types.name -> effect_type) =
  fun ename ->
    let ename1 = FStar_Reflection_V1_Derived.flatten_name ename in
    if ename1 = pure_effect_qn
    then E_PURE
    else
      if ename1 = pure_hoare_effect_qn
      then E_Pure
      else
        if ename1 = stack_effect_qn
        then E_Stack
        else if ename1 = st_effect_qn then E_ST else E_Unknown
let (effect_type_is_pure : effect_type -> Prims.bool) =
  fun etype ->
    match etype with
    | E_Total -> true
    | E_GTotal -> true
    | E_Lemma -> true
    | E_PURE -> true
    | E_Pure -> true
    | E_Stack -> false
    | E_ST -> false
    | E_Unknown -> false
type type_info =
  {
  ty: FStarC_Reflection_Types.typ ;
  refin: FStarC_Reflection_Types.term FStar_Pervasives_Native.option }
let (__proj__Mktype_info__item__ty :
  type_info -> FStarC_Reflection_Types.typ) =
  fun projectee -> match projectee with | { ty; refin;_} -> ty
let (__proj__Mktype_info__item__refin :
  type_info -> FStarC_Reflection_Types.term FStar_Pervasives_Native.option) =
  fun projectee -> match projectee with | { ty; refin;_} -> refin
let (mk_type_info :
  FStarC_Reflection_Types.typ ->
    FStarC_Reflection_Types.term FStar_Pervasives_Native.option -> type_info)
  = fun uu___ -> fun uu___1 -> { ty = uu___; refin = uu___1 }
let (type_info_to_string :
  type_info -> (Prims.string, unit) FStar_Tactics_Effect.tac_repr) =
  fun info ->
    let uu___ =
      let uu___1 = FStarC_Tactics_V1_Builtins.term_to_string info.ty in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range
                 "FStar.InteractiveHelpers.ExploreTerm.fst"
                 (Prims.of_int (84)) (Prims.of_int (2)) (Prims.of_int (84))
                 (Prims.of_int (24)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range
                 "FStar.InteractiveHelpers.ExploreTerm.fst"
                 (Prims.of_int (84)) (Prims.of_int (2)) (Prims.of_int (85))
                 (Prims.of_int (50))))) (Obj.magic uu___1)
        (fun uu___2 ->
           (fun uu___2 ->
              let uu___3 =
                let uu___4 =
                  let uu___5 =
                    FStar_InteractiveHelpers_Base.option_to_string
                      FStarC_Tactics_V1_Builtins.term_to_string info.refin in
                  FStar_Tactics_Effect.tac_bind
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range
                             "FStar.InteractiveHelpers.ExploreTerm.fst"
                             (Prims.of_int (85)) (Prims.of_int (2))
                             (Prims.of_int (85)) (Prims.of_int (44)))))
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Prims.fst"
                             (Prims.of_int (611)) (Prims.of_int (19))
                             (Prims.of_int (611)) (Prims.of_int (31)))))
                    (Obj.magic uu___5)
                    (fun uu___6 ->
                       FStar_Tactics_Effect.lift_div_tac
                         (fun uu___7 -> Prims.strcat uu___6 ")")) in
                FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range
                           "FStar.InteractiveHelpers.ExploreTerm.fst"
                           (Prims.of_int (85)) (Prims.of_int (2))
                           (Prims.of_int (85)) (Prims.of_int (50)))))
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
                            "FStar.InteractiveHelpers.ExploreTerm.fst"
                            (Prims.of_int (84)) (Prims.of_int (27))
                            (Prims.of_int (85)) (Prims.of_int (50)))))
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
            (FStar_Range.mk_range "FStar.InteractiveHelpers.ExploreTerm.fst"
               (Prims.of_int (84)) (Prims.of_int (2)) (Prims.of_int (85))
               (Prims.of_int (50)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Prims.fst" (Prims.of_int (611))
               (Prims.of_int (19)) (Prims.of_int (611)) (Prims.of_int (31)))))
      (Obj.magic uu___)
      (fun uu___1 ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___2 -> Prims.strcat "Mktype_info (" uu___1))
let (unit_type_info : type_info) =
  mk_type_info
    (FStarC_Reflection_V2_Builtins.pack_ln
       (FStarC_Reflection_V2_Data.Tv_FVar
          (FStarC_Reflection_V2_Builtins.pack_fv ["Prims"; "unit"])))
    FStar_Pervasives_Native.None
let (safe_tc :
  FStarC_Reflection_Types.env ->
    FStarC_Reflection_Types.term ->
      (FStarC_Reflection_Types.term FStar_Pervasives_Native.option, unit)
        FStar_Tactics_Effect.tac_repr)
  =
  fun e ->
    fun t ->
      FStar_Tactics_V1_Derived.try_with
        (fun uu___ ->
           match () with
           | () ->
               let uu___1 = FStarC_Tactics_V1_Builtins.tc e t in
               FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range
                          "FStar.InteractiveHelpers.ExploreTerm.fst"
                          (Prims.of_int (91)) (Prims.of_int (11))
                          (Prims.of_int (91)) (Prims.of_int (19)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range
                          "FStar.InteractiveHelpers.ExploreTerm.fst"
                          (Prims.of_int (91)) (Prims.of_int (6))
                          (Prims.of_int (91)) (Prims.of_int (19)))))
                 (Obj.magic uu___1)
                 (fun uu___2 ->
                    FStar_Tactics_Effect.lift_div_tac
                      (fun uu___3 -> FStar_Pervasives_Native.Some uu___2)))
        (fun uu___ ->
           (fun uu___ ->
              Obj.magic
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___1 -> FStar_Pervasives_Native.None))) uu___)
let (safe_tcc :
  FStarC_Reflection_Types.env ->
    FStarC_Reflection_Types.term ->
      (FStarC_Reflection_Types.comp FStar_Pervasives_Native.option, unit)
        FStar_Tactics_Effect.tac_repr)
  =
  fun e ->
    fun t ->
      FStar_Tactics_V1_Derived.try_with
        (fun uu___ ->
           match () with
           | () ->
               let uu___1 = FStarC_Tactics_V1_Builtins.tcc e t in
               FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range
                          "FStar.InteractiveHelpers.ExploreTerm.fst"
                          (Prims.of_int (95)) (Prims.of_int (11))
                          (Prims.of_int (95)) (Prims.of_int (20)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range
                          "FStar.InteractiveHelpers.ExploreTerm.fst"
                          (Prims.of_int (95)) (Prims.of_int (6))
                          (Prims.of_int (95)) (Prims.of_int (20)))))
                 (Obj.magic uu___1)
                 (fun uu___2 ->
                    FStar_Tactics_Effect.lift_div_tac
                      (fun uu___3 -> FStar_Pervasives_Native.Some uu___2)))
        (fun uu___ ->
           (fun uu___ ->
              Obj.magic
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___1 -> FStar_Pervasives_Native.None))) uu___)
let (get_type_info_from_type :
  FStarC_Reflection_Types.typ ->
    (type_info, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun ty ->
    let uu___ = FStarC_Tactics_V1_Builtins.inspect ty in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.InteractiveHelpers.ExploreTerm.fst"
               (Prims.of_int (98)) (Prims.of_int (8)) (Prims.of_int (98))
               (Prims.of_int (18)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.InteractiveHelpers.ExploreTerm.fst"
               (Prims.of_int (98)) (Prims.of_int (2)) (Prims.of_int (107))
               (Prims.of_int (24))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun uu___1 ->
            match uu___1 with
            | FStarC_Reflection_V1_Data.Tv_Refine (bv, sort, refin) ->
                let uu___2 =
                  FStar_InteractiveHelpers_Base.prettify_term false sort in
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.InteractiveHelpers.ExploreTerm.fst"
                              (Prims.of_int (100)) (Prims.of_int (19))
                              (Prims.of_int (100)) (Prims.of_int (43)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.InteractiveHelpers.ExploreTerm.fst"
                              (Prims.of_int (100)) (Prims.of_int (47))
                              (Prims.of_int (104)) (Prims.of_int (38)))))
                     (Obj.magic uu___2)
                     (fun uu___3 ->
                        (fun raw_type ->
                           let uu___3 =
                             Obj.magic
                               (FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___4 ->
                                     FStar_Reflection_V1_Derived.mk_binder bv
                                       sort)) in
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.InteractiveHelpers.ExploreTerm.fst"
                                         (Prims.of_int (101))
                                         (Prims.of_int (21))
                                         (Prims.of_int (101))
                                         (Prims.of_int (38)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.InteractiveHelpers.ExploreTerm.fst"
                                         (Prims.of_int (101))
                                         (Prims.of_int (41))
                                         (Prims.of_int (104))
                                         (Prims.of_int (38)))))
                                (Obj.magic uu___3)
                                (fun uu___4 ->
                                   (fun b ->
                                      let uu___4 =
                                        FStar_InteractiveHelpers_Base.prettify_term
                                          false refin in
                                      Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                    (Prims.of_int (102))
                                                    (Prims.of_int (16))
                                                    (Prims.of_int (102))
                                                    (Prims.of_int (41)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                    (Prims.of_int (102))
                                                    (Prims.of_int (44))
                                                    (Prims.of_int (104))
                                                    (Prims.of_int (38)))))
                                           (Obj.magic uu___4)
                                           (fun uu___5 ->
                                              (fun refin1 ->
                                                 let uu___5 =
                                                   FStarC_Tactics_V1_Builtins.pack
                                                     (FStarC_Reflection_V1_Data.Tv_Abs
                                                        (b, refin1)) in
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                               (Prims.of_int (103))
                                                               (Prims.of_int (16))
                                                               (Prims.of_int (103))
                                                               (Prims.of_int (37)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                               (Prims.of_int (104))
                                                               (Prims.of_int (4))
                                                               (Prims.of_int (104))
                                                               (Prims.of_int (38)))))
                                                      (Obj.magic uu___5)
                                                      (fun refin2 ->
                                                         FStar_Tactics_Effect.lift_div_tac
                                                           (fun uu___6 ->
                                                              mk_type_info
                                                                raw_type
                                                                (FStar_Pervasives_Native.Some
                                                                   refin2)))))
                                                uu___5))) uu___4))) uu___3))
            | uu___2 ->
                let uu___3 =
                  FStar_InteractiveHelpers_Base.prettify_term false ty in
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.InteractiveHelpers.ExploreTerm.fst"
                              (Prims.of_int (106)) (Prims.of_int (13))
                              (Prims.of_int (106)) (Prims.of_int (35)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.InteractiveHelpers.ExploreTerm.fst"
                              (Prims.of_int (107)) (Prims.of_int (4))
                              (Prims.of_int (107)) (Prims.of_int (24)))))
                     (Obj.magic uu___3)
                     (fun ty1 ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___4 ->
                             mk_type_info ty1 FStar_Pervasives_Native.None))))
           uu___1)
let (get_type_info :
  FStarC_Reflection_Types.env ->
    FStarC_Reflection_Types.term ->
      (type_info FStar_Pervasives_Native.option, unit)
        FStar_Tactics_Effect.tac_repr)
  =
  fun e ->
    fun t ->
      let uu___ = safe_tc e t in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range
                 "FStar.InteractiveHelpers.ExploreTerm.fst"
                 (Prims.of_int (111)) (Prims.of_int (8)) (Prims.of_int (111))
                 (Prims.of_int (19)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range
                 "FStar.InteractiveHelpers.ExploreTerm.fst"
                 (Prims.of_int (111)) (Prims.of_int (2)) (Prims.of_int (113))
                 (Prims.of_int (48))))) (Obj.magic uu___)
        (fun uu___1 ->
           (fun uu___1 ->
              match uu___1 with
              | FStar_Pervasives_Native.None ->
                  Obj.magic
                    (Obj.repr
                       (FStar_Tactics_Effect.lift_div_tac
                          (fun uu___2 -> FStar_Pervasives_Native.None)))
              | FStar_Pervasives_Native.Some ty ->
                  Obj.magic
                    (Obj.repr
                       (let uu___2 = get_type_info_from_type ty in
                        FStar_Tactics_Effect.tac_bind
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "FStar.InteractiveHelpers.ExploreTerm.fst"
                                   (Prims.of_int (113)) (Prims.of_int (20))
                                   (Prims.of_int (113)) (Prims.of_int (48)))))
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "FStar.InteractiveHelpers.ExploreTerm.fst"
                                   (Prims.of_int (113)) (Prims.of_int (15))
                                   (Prims.of_int (113)) (Prims.of_int (48)))))
                          (Obj.magic uu___2)
                          (fun uu___3 ->
                             FStar_Tactics_Effect.lift_div_tac
                               (fun uu___4 ->
                                  FStar_Pervasives_Native.Some uu___3)))))
             uu___1)
let (get_total_or_gtotal_ret_type :
  FStarC_Reflection_Types.comp ->
    FStarC_Reflection_Types.typ FStar_Pervasives_Native.option)
  =
  fun c ->
    match FStarC_Reflection_V1_Builtins.inspect_comp c with
    | FStarC_Reflection_V1_Data.C_Total ret_ty ->
        FStar_Pervasives_Native.Some ret_ty
    | FStarC_Reflection_V1_Data.C_GTotal ret_ty ->
        FStar_Pervasives_Native.Some ret_ty
    | uu___ -> FStar_Pervasives_Native.None
let (get_comp_ret_type :
  FStarC_Reflection_Types.comp -> FStarC_Reflection_Types.typ) =
  fun c ->
    match FStarC_Reflection_V1_Builtins.inspect_comp c with
    | FStarC_Reflection_V1_Data.C_Total ret_ty -> ret_ty
    | FStarC_Reflection_V1_Data.C_GTotal ret_ty -> ret_ty
    | FStarC_Reflection_V1_Data.C_Eff (uu___, uu___1, ret_ty, uu___2, uu___3)
        -> ret_ty
    | FStarC_Reflection_V1_Data.C_Lemma (uu___, uu___1, uu___2) ->
        FStarC_Reflection_V2_Builtins.pack_ln
          (FStarC_Reflection_V2_Data.Tv_FVar
             (FStarC_Reflection_V2_Builtins.pack_fv ["Prims"; "unit"]))
let (is_total_or_gtotal : FStarC_Reflection_Types.comp -> Prims.bool) =
  fun c ->
    FStar_Pervasives_Native.uu___is_Some (get_total_or_gtotal_ret_type c)
let (is_unit_type :
  FStarC_Reflection_Types.typ ->
    (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun ty ->
    let uu___ = FStarC_Tactics_V1_Builtins.inspect ty in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.InteractiveHelpers.ExploreTerm.fst"
               (Prims.of_int (135)) (Prims.of_int (8)) (Prims.of_int (135))
               (Prims.of_int (18)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.InteractiveHelpers.ExploreTerm.fst"
               (Prims.of_int (135)) (Prims.of_int (2)) (Prims.of_int (137))
               (Prims.of_int (14))))) (Obj.magic uu___)
      (fun uu___1 ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___2 ->
              match uu___1 with
              | FStarC_Reflection_V1_Data.Tv_FVar fv ->
                  FStar_InteractiveHelpers_Base.fv_eq_name fv
                    FStar_Reflection_Const.unit_lid
              | uu___3 -> false))
type typ_or_comp =
  | TC_Typ of FStarC_Reflection_Types.typ * FStarC_Reflection_Types.binder
  Prims.list * Prims.nat 
  | TC_Comp of FStarC_Reflection_Types.comp * FStarC_Reflection_Types.binder
  Prims.list * Prims.nat 
let (uu___is_TC_Typ : typ_or_comp -> Prims.bool) =
  fun projectee ->
    match projectee with
    | TC_Typ (v, pl, num_unflushed) -> true
    | uu___ -> false
let (__proj__TC_Typ__item__v : typ_or_comp -> FStarC_Reflection_Types.typ) =
  fun projectee -> match projectee with | TC_Typ (v, pl, num_unflushed) -> v
let (__proj__TC_Typ__item__pl :
  typ_or_comp -> FStarC_Reflection_Types.binder Prims.list) =
  fun projectee -> match projectee with | TC_Typ (v, pl, num_unflushed) -> pl
let (__proj__TC_Typ__item__num_unflushed : typ_or_comp -> Prims.nat) =
  fun projectee ->
    match projectee with | TC_Typ (v, pl, num_unflushed) -> num_unflushed
let (uu___is_TC_Comp : typ_or_comp -> Prims.bool) =
  fun projectee ->
    match projectee with
    | TC_Comp (v, pl, num_unflushed) -> true
    | uu___ -> false
let (__proj__TC_Comp__item__v : typ_or_comp -> FStarC_Reflection_Types.comp)
  =
  fun projectee -> match projectee with | TC_Comp (v, pl, num_unflushed) -> v
let (__proj__TC_Comp__item__pl :
  typ_or_comp -> FStarC_Reflection_Types.binder Prims.list) =
  fun projectee ->
    match projectee with | TC_Comp (v, pl, num_unflushed) -> pl
let (__proj__TC_Comp__item__num_unflushed : typ_or_comp -> Prims.nat) =
  fun projectee ->
    match projectee with | TC_Comp (v, pl, num_unflushed) -> num_unflushed
let (typ_or_comp_to_string :
  typ_or_comp -> (Prims.string, unit) FStar_Tactics_Effect.tac_repr) =
  fun tyc ->
    match tyc with
    | TC_Typ (v, pl, num_unflushed) ->
        let uu___ =
          let uu___1 = FStarC_Tactics_V1_Builtins.term_to_string v in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range
                     "FStar.InteractiveHelpers.ExploreTerm.fst"
                     (Prims.of_int (163)) (Prims.of_int (17))
                     (Prims.of_int (163)) (Prims.of_int (33)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range
                     "FStar.InteractiveHelpers.ExploreTerm.fst"
                     (Prims.of_int (163)) (Prims.of_int (17))
                     (Prims.of_int (164)) (Prims.of_int (37)))))
            (Obj.magic uu___1)
            (fun uu___2 ->
               (fun uu___2 ->
                  let uu___3 =
                    let uu___4 =
                      let uu___5 =
                        FStar_InteractiveHelpers_Base.list_to_string
                          (fun b -> FStar_Tactics_V1_Derived.name_of_binder b)
                          pl in
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.InteractiveHelpers.ExploreTerm.fst"
                                 (Prims.of_int (163)) (Prims.of_int (43))
                                 (Prims.of_int (163)) (Prims.of_int (88)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "Prims.fst"
                                 (Prims.of_int (611)) (Prims.of_int (19))
                                 (Prims.of_int (611)) (Prims.of_int (31)))))
                        (Obj.magic uu___5)
                        (fun uu___6 ->
                           FStar_Tactics_Effect.lift_div_tac
                             (fun uu___7 ->
                                Prims.strcat uu___6
                                  (Prims.strcat " "
                                     (Prims.string_of_int num_unflushed)))) in
                    FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range
                               "FStar.InteractiveHelpers.ExploreTerm.fst"
                               (Prims.of_int (163)) (Prims.of_int (43))
                               (Prims.of_int (164)) (Prims.of_int (37)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Prims.fst"
                               (Prims.of_int (611)) (Prims.of_int (19))
                               (Prims.of_int (611)) (Prims.of_int (31)))))
                      (Obj.magic uu___4)
                      (fun uu___5 ->
                         FStar_Tactics_Effect.lift_div_tac
                           (fun uu___6 -> Prims.strcat ") " uu___5)) in
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.InteractiveHelpers.ExploreTerm.fst"
                                (Prims.of_int (163)) (Prims.of_int (36))
                                (Prims.of_int (164)) (Prims.of_int (37)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Prims.fst"
                                (Prims.of_int (611)) (Prims.of_int (19))
                                (Prims.of_int (611)) (Prims.of_int (31)))))
                       (Obj.magic uu___3)
                       (fun uu___4 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___5 -> Prims.strcat uu___2 uu___4))))
                 uu___2) in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range
                   "FStar.InteractiveHelpers.ExploreTerm.fst"
                   (Prims.of_int (163)) (Prims.of_int (17))
                   (Prims.of_int (164)) (Prims.of_int (37)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Prims.fst" (Prims.of_int (611))
                   (Prims.of_int (19)) (Prims.of_int (611))
                   (Prims.of_int (31))))) (Obj.magic uu___)
          (fun uu___1 ->
             FStar_Tactics_Effect.lift_div_tac
               (fun uu___2 -> Prims.strcat "TC_Typ (" uu___1))
    | TC_Comp (c, pl, num_unflushed) ->
        let uu___ =
          let uu___1 = FStar_InteractiveHelpers_Base.acomp_to_string c in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range
                     "FStar.InteractiveHelpers.ExploreTerm.fst"
                     (Prims.of_int (166)) (Prims.of_int (18))
                     (Prims.of_int (166)) (Prims.of_int (35)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range
                     "FStar.InteractiveHelpers.ExploreTerm.fst"
                     (Prims.of_int (166)) (Prims.of_int (18))
                     (Prims.of_int (167)) (Prims.of_int (37)))))
            (Obj.magic uu___1)
            (fun uu___2 ->
               (fun uu___2 ->
                  let uu___3 =
                    let uu___4 =
                      let uu___5 =
                        FStar_InteractiveHelpers_Base.list_to_string
                          (fun b -> FStar_Tactics_V1_Derived.name_of_binder b)
                          pl in
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.InteractiveHelpers.ExploreTerm.fst"
                                 (Prims.of_int (166)) (Prims.of_int (45))
                                 (Prims.of_int (166)) (Prims.of_int (90)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "Prims.fst"
                                 (Prims.of_int (611)) (Prims.of_int (19))
                                 (Prims.of_int (611)) (Prims.of_int (31)))))
                        (Obj.magic uu___5)
                        (fun uu___6 ->
                           FStar_Tactics_Effect.lift_div_tac
                             (fun uu___7 ->
                                Prims.strcat uu___6
                                  (Prims.strcat " "
                                     (Prims.string_of_int num_unflushed)))) in
                    FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range
                               "FStar.InteractiveHelpers.ExploreTerm.fst"
                               (Prims.of_int (166)) (Prims.of_int (45))
                               (Prims.of_int (167)) (Prims.of_int (37)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Prims.fst"
                               (Prims.of_int (611)) (Prims.of_int (19))
                               (Prims.of_int (611)) (Prims.of_int (31)))))
                      (Obj.magic uu___4)
                      (fun uu___5 ->
                         FStar_Tactics_Effect.lift_div_tac
                           (fun uu___6 -> Prims.strcat ") " uu___5)) in
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.InteractiveHelpers.ExploreTerm.fst"
                                (Prims.of_int (166)) (Prims.of_int (38))
                                (Prims.of_int (167)) (Prims.of_int (37)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Prims.fst"
                                (Prims.of_int (611)) (Prims.of_int (19))
                                (Prims.of_int (611)) (Prims.of_int (31)))))
                       (Obj.magic uu___3)
                       (fun uu___4 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___5 -> Prims.strcat uu___2 uu___4))))
                 uu___2) in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range
                   "FStar.InteractiveHelpers.ExploreTerm.fst"
                   (Prims.of_int (166)) (Prims.of_int (18))
                   (Prims.of_int (167)) (Prims.of_int (37)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Prims.fst" (Prims.of_int (611))
                   (Prims.of_int (19)) (Prims.of_int (611))
                   (Prims.of_int (31))))) (Obj.magic uu___)
          (fun uu___1 ->
             FStar_Tactics_Effect.lift_div_tac
               (fun uu___2 -> Prims.strcat "TC_Comp (" uu___1))
let (params_of_typ_or_comp :
  typ_or_comp -> FStarC_Reflection_Types.binder Prims.list) =
  fun c ->
    match c with
    | TC_Typ (uu___, pl, uu___1) -> pl
    | TC_Comp (uu___, pl, uu___1) -> pl
let (num_unflushed_of_typ_or_comp : typ_or_comp -> Prims.nat) =
  fun c ->
    match c with
    | TC_Typ (uu___, uu___1, n) -> n
    | TC_Comp (uu___, uu___1, n) -> n
let (safe_typ_or_comp :
  Prims.bool ->
    FStarC_Reflection_Types.env ->
      FStarC_Reflection_Types.term ->
        (typ_or_comp FStar_Pervasives_Native.option, unit)
          FStar_Tactics_Effect.tac_repr)
  =
  fun dbg ->
    fun e ->
      fun t ->
        let uu___ = safe_tcc e t in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range
                   "FStar.InteractiveHelpers.ExploreTerm.fst"
                   (Prims.of_int (183)) (Prims.of_int (8))
                   (Prims.of_int (183)) (Prims.of_int (20)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range
                   "FStar.InteractiveHelpers.ExploreTerm.fst"
                   (Prims.of_int (183)) (Prims.of_int (2))
                   (Prims.of_int (193)) (Prims.of_int (25)))))
          (Obj.magic uu___)
          (fun uu___1 ->
             (fun uu___1 ->
                match uu___1 with
                | FStar_Pervasives_Native.None ->
                    let uu___2 =
                      let uu___3 =
                        let uu___4 =
                          let uu___5 =
                            let uu___6 =
                              FStarC_Tactics_V1_Builtins.term_to_string t in
                            FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "FStar.InteractiveHelpers.ExploreTerm.fst"
                                       (Prims.of_int (186))
                                       (Prims.of_int (33))
                                       (Prims.of_int (186))
                                       (Prims.of_int (49)))))
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
                                      Prims.strcat uu___7 "\n-comp: None")) in
                          FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.InteractiveHelpers.ExploreTerm.fst"
                                     (Prims.of_int (186)) (Prims.of_int (33))
                                     (Prims.of_int (187)) (Prims.of_int (34)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range "Prims.fst"
                                     (Prims.of_int (611)) (Prims.of_int (19))
                                     (Prims.of_int (611)) (Prims.of_int (31)))))
                            (Obj.magic uu___5)
                            (fun uu___6 ->
                               FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___7 ->
                                    Prims.strcat "\n-term: " uu___6)) in
                        FStar_Tactics_Effect.tac_bind
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "FStar.InteractiveHelpers.ExploreTerm.fst"
                                   (Prims.of_int (186)) (Prims.of_int (19))
                                   (Prims.of_int (187)) (Prims.of_int (34)))))
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range "Prims.fst"
                                   (Prims.of_int (611)) (Prims.of_int (19))
                                   (Prims.of_int (611)) (Prims.of_int (31)))))
                          (Obj.magic uu___4)
                          (fun uu___5 ->
                             FStar_Tactics_Effect.lift_div_tac
                               (fun uu___6 ->
                                  Prims.strcat "[> safe_typ_or_comp:" uu___5)) in
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.InteractiveHelpers.ExploreTerm.fst"
                                 (Prims.of_int (185)) (Prims.of_int (18))
                                 (Prims.of_int (187)) (Prims.of_int (35)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.InteractiveHelpers.ExploreTerm.fst"
                                 (Prims.of_int (185)) (Prims.of_int (4))
                                 (Prims.of_int (187)) (Prims.of_int (35)))))
                        (Obj.magic uu___3)
                        (fun uu___4 ->
                           (fun uu___4 ->
                              Obj.magic
                                (FStar_InteractiveHelpers_Base.print_dbg dbg
                                   uu___4)) uu___4) in
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.InteractiveHelpers.ExploreTerm.fst"
                                  (Prims.of_int (185)) (Prims.of_int (4))
                                  (Prims.of_int (187)) (Prims.of_int (35)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.InteractiveHelpers.ExploreTerm.fst"
                                  (Prims.of_int (188)) (Prims.of_int (4))
                                  (Prims.of_int (188)) (Prims.of_int (8)))))
                         (Obj.magic uu___2)
                         (fun uu___3 ->
                            FStar_Tactics_Effect.lift_div_tac
                              (fun uu___4 -> FStar_Pervasives_Native.None)))
                | FStar_Pervasives_Native.Some c ->
                    let uu___2 =
                      let uu___3 =
                        let uu___4 =
                          let uu___5 =
                            let uu___6 =
                              FStarC_Tactics_V1_Builtins.term_to_string t in
                            FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "FStar.InteractiveHelpers.ExploreTerm.fst"
                                       (Prims.of_int (191))
                                       (Prims.of_int (33))
                                       (Prims.of_int (191))
                                       (Prims.of_int (49)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "FStar.InteractiveHelpers.ExploreTerm.fst"
                                       (Prims.of_int (191))
                                       (Prims.of_int (33))
                                       (Prims.of_int (192))
                                       (Prims.of_int (50)))))
                              (Obj.magic uu___6)
                              (fun uu___7 ->
                                 (fun uu___7 ->
                                    let uu___8 =
                                      let uu___9 =
                                        FStar_InteractiveHelpers_Base.acomp_to_string
                                          c in
                                      FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                 (Prims.of_int (192))
                                                 (Prims.of_int (33))
                                                 (Prims.of_int (192))
                                                 (Prims.of_int (50)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Prims.fst"
                                                 (Prims.of_int (611))
                                                 (Prims.of_int (19))
                                                 (Prims.of_int (611))
                                                 (Prims.of_int (31)))))
                                        (Obj.magic uu___9)
                                        (fun uu___10 ->
                                           FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___11 ->
                                                Prims.strcat "\n-comp: "
                                                  uu___10)) in
                                    Obj.magic
                                      (FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                  (Prims.of_int (192))
                                                  (Prims.of_int (19))
                                                  (Prims.of_int (192))
                                                  (Prims.of_int (50)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Prims.fst"
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
                                  (FStar_Range.mk_range
                                     "FStar.InteractiveHelpers.ExploreTerm.fst"
                                     (Prims.of_int (191)) (Prims.of_int (33))
                                     (Prims.of_int (192)) (Prims.of_int (50)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range "Prims.fst"
                                     (Prims.of_int (611)) (Prims.of_int (19))
                                     (Prims.of_int (611)) (Prims.of_int (31)))))
                            (Obj.magic uu___5)
                            (fun uu___6 ->
                               FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___7 ->
                                    Prims.strcat "\n-term: " uu___6)) in
                        FStar_Tactics_Effect.tac_bind
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "FStar.InteractiveHelpers.ExploreTerm.fst"
                                   (Prims.of_int (191)) (Prims.of_int (19))
                                   (Prims.of_int (192)) (Prims.of_int (50)))))
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range "Prims.fst"
                                   (Prims.of_int (611)) (Prims.of_int (19))
                                   (Prims.of_int (611)) (Prims.of_int (31)))))
                          (Obj.magic uu___4)
                          (fun uu___5 ->
                             FStar_Tactics_Effect.lift_div_tac
                               (fun uu___6 ->
                                  Prims.strcat "[> safe_typ_or_comp:" uu___5)) in
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.InteractiveHelpers.ExploreTerm.fst"
                                 (Prims.of_int (190)) (Prims.of_int (18))
                                 (Prims.of_int (192)) (Prims.of_int (51)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.InteractiveHelpers.ExploreTerm.fst"
                                 (Prims.of_int (190)) (Prims.of_int (4))
                                 (Prims.of_int (192)) (Prims.of_int (51)))))
                        (Obj.magic uu___3)
                        (fun uu___4 ->
                           (fun uu___4 ->
                              Obj.magic
                                (FStar_InteractiveHelpers_Base.print_dbg dbg
                                   uu___4)) uu___4) in
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.InteractiveHelpers.ExploreTerm.fst"
                                  (Prims.of_int (190)) (Prims.of_int (4))
                                  (Prims.of_int (192)) (Prims.of_int (51)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.InteractiveHelpers.ExploreTerm.fst"
                                  (Prims.of_int (193)) (Prims.of_int (4))
                                  (Prims.of_int (193)) (Prims.of_int (25)))))
                         (Obj.magic uu___2)
                         (fun uu___3 ->
                            FStar_Tactics_Effect.lift_div_tac
                              (fun uu___4 ->
                                 FStar_Pervasives_Native.Some
                                   (TC_Comp (c, [], Prims.int_zero))))))
               uu___1)
let (subst_bv_in_comp :
  FStarC_Reflection_Types.env ->
    FStarC_Reflection_Types.bv ->
      FStarC_Reflection_Types.typ ->
        FStarC_Reflection_Types.term ->
          FStarC_Reflection_Types.comp ->
            (FStarC_Reflection_Types.comp, unit)
              FStar_Tactics_Effect.tac_repr)
  =
  fun e ->
    fun b ->
      fun sort ->
        fun t ->
          fun c ->
            FStar_InteractiveHelpers_Base.apply_subst_in_comp e c
              [((b, sort), t)]
let (subst_binder_in_comp :
  FStarC_Reflection_Types.env ->
    FStarC_Reflection_Types.binder ->
      FStarC_Reflection_Types.term ->
        FStarC_Reflection_Types.comp ->
          (FStarC_Reflection_Types.comp, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun e ->
    fun b ->
      fun t ->
        fun c ->
          let uu___ = FStar_Tactics_V1_Derived.binder_sort b in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range
                     "FStar.InteractiveHelpers.ExploreTerm.fst"
                     (Prims.of_int (201)) (Prims.of_int (38))
                     (Prims.of_int (201)) (Prims.of_int (53)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range
                     "FStar.InteractiveHelpers.ExploreTerm.fst"
                     (Prims.of_int (201)) (Prims.of_int (2))
                     (Prims.of_int (201)) (Prims.of_int (57)))))
            (Obj.magic uu___)
            (fun uu___1 ->
               (fun uu___1 ->
                  Obj.magic
                    (subst_bv_in_comp e
                       (FStar_Reflection_V1_Derived.bv_of_binder b) uu___1 t
                       c)) uu___1)
let rec (unfold_until_arrow :
  FStarC_Reflection_Types.env ->
    FStarC_Reflection_Types.typ ->
      (FStarC_Reflection_Types.typ, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun e ->
    fun ty0 ->
      let uu___ =
        let uu___1 = FStarC_Tactics_V1_Builtins.inspect ty0 in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range
                   "FStar.InteractiveHelpers.ExploreTerm.fst"
                   (Prims.of_int (207)) (Prims.of_int (15))
                   (Prims.of_int (207)) (Prims.of_int (28)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range
                   "FStar.InteractiveHelpers.ExploreTerm.fst"
                   (Prims.of_int (207)) (Prims.of_int (5))
                   (Prims.of_int (207)) (Prims.of_int (28)))))
          (Obj.magic uu___1)
          (fun uu___2 ->
             FStar_Tactics_Effect.lift_div_tac
               (fun uu___3 ->
                  FStarC_Reflection_V1_Data.uu___is_Tv_Arrow uu___2)) in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range
                 "FStar.InteractiveHelpers.ExploreTerm.fst"
                 (Prims.of_int (207)) (Prims.of_int (5)) (Prims.of_int (207))
                 (Prims.of_int (28)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range
                 "FStar.InteractiveHelpers.ExploreTerm.fst"
                 (Prims.of_int (207)) (Prims.of_int (2)) (Prims.of_int (251))
                 (Prims.of_int (7))))) (Obj.magic uu___)
        (fun uu___1 ->
           (fun uu___1 ->
              if uu___1
              then
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> ty0)))
              else
                Obj.magic
                  (Obj.repr
                     (let uu___3 =
                        FStarC_Tactics_V1_Builtins.norm_term_env e [] ty0 in
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.InteractiveHelpers.ExploreTerm.fst"
                                 (Prims.of_int (211)) (Prims.of_int (13))
                                 (Prims.of_int (211)) (Prims.of_int (35)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.InteractiveHelpers.ExploreTerm.fst"
                                 (Prims.of_int (211)) (Prims.of_int (38))
                                 (Prims.of_int (250)) (Prims.of_int (75)))))
                        (Obj.magic uu___3)
                        (fun uu___4 ->
                           (fun ty ->
                              let uu___4 =
                                Obj.magic
                                  (FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___5 ->
                                        fun fv ->
                                          let uu___6 =
                                            FStarC_Tactics_V1_Builtins.pack
                                              (FStarC_Reflection_V1_Data.Tv_FVar
                                                 fv) in
                                          FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                     (Prims.of_int (214))
                                                     (Prims.of_int (15))
                                                     (Prims.of_int (214))
                                                     (Prims.of_int (32)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                     (Prims.of_int (214))
                                                     (Prims.of_int (35))
                                                     (Prims.of_int (224))
                                                     (Prims.of_int (9)))))
                                            (Obj.magic uu___6)
                                            (fun uu___7 ->
                                               (fun ty1 ->
                                                  let uu___7 =
                                                    Obj.magic
                                                      (FStar_Tactics_Effect.lift_div_tac
                                                         (fun uu___8 ->
                                                            FStar_Reflection_V1_Derived.flatten_name
                                                              (FStarC_Reflection_V1_Builtins.inspect_fv
                                                                 fv))) in
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                (Prims.of_int (215))
                                                                (Prims.of_int (16))
                                                                (Prims.of_int (215))
                                                                (Prims.of_int (44)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                (Prims.of_int (215))
                                                                (Prims.of_int (47))
                                                                (Prims.of_int (224))
                                                                (Prims.of_int (9)))))
                                                       (Obj.magic uu___7)
                                                       (fun uu___8 ->
                                                          (fun fvn ->
                                                             let uu___8 =
                                                               FStarC_Tactics_V1_Builtins.norm_term_env
                                                                 e
                                                                 [FStar_Pervasives.delta_only
                                                                    [fvn]]
                                                                 ty1 in
                                                             Obj.magic
                                                               (FStar_Tactics_Effect.tac_bind
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (217))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (217))
                                                                    (Prims.of_int (53)))))
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (219))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (223))
                                                                    (Prims.of_int (16)))))
                                                                  (Obj.magic
                                                                    uu___8)
                                                                  (fun uu___9
                                                                    ->
                                                                    (fun ty'
                                                                    ->
                                                                    let uu___9
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.inspect
                                                                    ty' in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (219))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (219))
                                                                    (Prims.of_int (29)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (219))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (223))
                                                                    (Prims.of_int (16)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    match uu___10
                                                                    with
                                                                    | 
                                                                    FStarC_Reflection_V1_Data.Tv_FVar
                                                                    fv' ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (if
                                                                    (FStar_Reflection_V1_Derived.flatten_name
                                                                    (FStarC_Reflection_V1_Builtins.inspect_fv
                                                                    fv')) =
                                                                    fvn
                                                                    then
                                                                    Obj.repr
                                                                    (let uu___11
                                                                    =
                                                                    let uu___12
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.term_to_string
                                                                    ty0 in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (222))
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (222))
                                                                    (Prims.of_int (81)))))
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
                                                                    "unfold_until_arrow: could not unfold: "
                                                                    uu___13)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (222))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (222))
                                                                    (Prims.of_int (82)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (222))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (222))
                                                                    (Prims.of_int (82)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.mfail
                                                                    uu___12))
                                                                    uu___12))
                                                                    else
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    -> ty'))))
                                                                    | 
                                                                    uu___11
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    -> ty'))))
                                                                    uu___10)))
                                                                    uu___9)))
                                                            uu___8))) uu___7))) in
                              Obj.magic
                                (FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "FStar.InteractiveHelpers.ExploreTerm.fst"
                                            (Prims.of_int (213))
                                            (Prims.of_int (40))
                                            (Prims.of_int (224))
                                            (Prims.of_int (9)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "FStar.InteractiveHelpers.ExploreTerm.fst"
                                            (Prims.of_int (227))
                                            (Prims.of_int (4))
                                            (Prims.of_int (250))
                                            (Prims.of_int (75)))))
                                   (Obj.magic uu___4)
                                   (fun uu___5 ->
                                      (fun unfold_fv ->
                                         let uu___5 =
                                           FStarC_Tactics_V1_Builtins.inspect
                                             ty in
                                         Obj.magic
                                           (FStar_Tactics_Effect.tac_bind
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                       (Prims.of_int (227))
                                                       (Prims.of_int (10))
                                                       (Prims.of_int (227))
                                                       (Prims.of_int (20)))))
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                       (Prims.of_int (227))
                                                       (Prims.of_int (4))
                                                       (Prims.of_int (250))
                                                       (Prims.of_int (75)))))
                                              (Obj.magic uu___5)
                                              (fun uu___6 ->
                                                 (fun uu___6 ->
                                                    match uu___6 with
                                                    | FStarC_Reflection_V1_Data.Tv_Arrow
                                                        (uu___7, uu___8) ->
                                                        Obj.magic
                                                          (Obj.repr
                                                             (FStar_Tactics_Effect.lift_div_tac
                                                                (fun uu___9
                                                                   -> ty)))
                                                    | FStarC_Reflection_V1_Data.Tv_FVar
                                                        fv ->
                                                        Obj.magic
                                                          (Obj.repr
                                                             (let uu___7 =
                                                                unfold_fv fv in
                                                              FStar_Tactics_Effect.tac_bind
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (231))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (231))
                                                                    (Prims.of_int (28)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (232))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (232))
                                                                    (Prims.of_int (30)))))
                                                                (Obj.magic
                                                                   uu___7)
                                                                (fun uu___8
                                                                   ->
                                                                   (fun ty'
                                                                    ->
                                                                    Obj.magic
                                                                    (unfold_until_arrow
                                                                    e ty'))
                                                                    uu___8)))
                                                    | FStarC_Reflection_V1_Data.Tv_App
                                                        (uu___7, uu___8) ->
                                                        Obj.magic
                                                          (Obj.repr
                                                             (let uu___9 =
                                                                FStar_Tactics_V1_SyntaxHelpers.collect_app
                                                                  ty in
                                                              FStar_Tactics_Effect.tac_bind
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (235))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (235))
                                                                    (Prims.of_int (35)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (233))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (242))
                                                                    (Prims.of_int (9)))))
                                                                (Obj.magic
                                                                   uu___9)
                                                                (fun uu___10
                                                                   ->
                                                                   (fun
                                                                    uu___10
                                                                    ->
                                                                    match uu___10
                                                                    with
                                                                    | 
                                                                    (hd,
                                                                    args) ->
                                                                    let uu___11
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.inspect
                                                                    hd in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (236))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (236))
                                                                    (Prims.of_int (28)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (236))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (82)))))
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
                                                                    FStarC_Reflection_V1_Data.Tv_FVar
                                                                    fv ->
                                                                    let uu___13
                                                                    =
                                                                    unfold_fv
                                                                    fv in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (238))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (238))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (238))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (240))
                                                                    (Prims.of_int (32)))))
                                                                    (Obj.magic
                                                                    uu___13)
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    (fun hd'
                                                                    ->
                                                                    let uu___14
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    FStar_Reflection_V1_Derived.mk_app
                                                                    hd' args)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (239))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (239))
                                                                    (Prims.of_int (33)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (240))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (240))
                                                                    (Prims.of_int (32)))))
                                                                    (Obj.magic
                                                                    uu___14)
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    (fun ty'
                                                                    ->
                                                                    Obj.magic
                                                                    (unfold_until_arrow
                                                                    e ty'))
                                                                    uu___15)))
                                                                    uu___14))
                                                                    | 
                                                                    uu___13
                                                                    ->
                                                                    let uu___14
                                                                    =
                                                                    let uu___15
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.term_to_string
                                                                    ty0 in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (81)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___15)
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    Prims.strcat
                                                                    "unfold_until_arrow: could not unfold: "
                                                                    uu___16)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (82)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (82)))))
                                                                    (Obj.magic
                                                                    uu___14)
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.mfail
                                                                    uu___15))
                                                                    uu___15)))
                                                                    uu___12)))
                                                                    uu___10)))
                                                    | FStarC_Reflection_V1_Data.Tv_Refine
                                                        (bv, sort, ref) ->
                                                        Obj.magic
                                                          (Obj.repr
                                                             (unfold_until_arrow
                                                                e sort))
                                                    | FStarC_Reflection_V1_Data.Tv_AscribedT
                                                        (body, uu___7,
                                                         uu___8, uu___9)
                                                        ->
                                                        Obj.magic
                                                          (Obj.repr
                                                             (unfold_until_arrow
                                                                e body))
                                                    | FStarC_Reflection_V1_Data.Tv_AscribedC
                                                        (body, uu___7,
                                                         uu___8, uu___9)
                                                        ->
                                                        Obj.magic
                                                          (Obj.repr
                                                             (unfold_until_arrow
                                                                e body))
                                                    | uu___7 ->
                                                        Obj.magic
                                                          (Obj.repr
                                                             (let uu___8 =
                                                                let uu___9 =
                                                                  FStarC_Tactics_V1_Builtins.term_to_string
                                                                    ty0 in
                                                                FStar_Tactics_Effect.tac_bind
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (250))
                                                                    (Prims.of_int (56))
                                                                    (Prims.of_int (250))
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
                                                                    uu___9)
                                                                  (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    Prims.strcat
                                                                    "unfold_until_arrow: could not unfold: "
                                                                    uu___10)) in
                                                              FStar_Tactics_Effect.tac_bind
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (250))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (250))
                                                                    (Prims.of_int (75)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (250))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (250))
                                                                    (Prims.of_int (75)))))
                                                                (Obj.magic
                                                                   uu___8)
                                                                (fun uu___9
                                                                   ->
                                                                   (fun
                                                                    uu___9 ->
                                                                    Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.mfail
                                                                    uu___9))
                                                                    uu___9))))
                                                   uu___6))) uu___5))) uu___4))))
             uu___1)
let (inst_comp_once :
  FStarC_Reflection_Types.env ->
    FStarC_Reflection_Types.comp ->
      FStarC_Reflection_Types.term ->
        (FStarC_Reflection_Types.comp, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun e ->
    fun c ->
      fun t ->
        let uu___ =
          Obj.magic
            (FStar_Tactics_Effect.lift_div_tac
               (fun uu___1 -> get_comp_ret_type c)) in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range
                   "FStar.InteractiveHelpers.ExploreTerm.fst"
                   (Prims.of_int (256)) (Prims.of_int (11))
                   (Prims.of_int (256)) (Prims.of_int (30)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range
                   "FStar.InteractiveHelpers.ExploreTerm.fst"
                   (Prims.of_int (256)) (Prims.of_int (33))
                   (Prims.of_int (263)) (Prims.of_int (5)))))
          (Obj.magic uu___)
          (fun uu___1 ->
             (fun ty ->
                let uu___1 = unfold_until_arrow e ty in
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.InteractiveHelpers.ExploreTerm.fst"
                              (Prims.of_int (257)) (Prims.of_int (12))
                              (Prims.of_int (257)) (Prims.of_int (35)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.InteractiveHelpers.ExploreTerm.fst"
                              (Prims.of_int (258)) (Prims.of_int (8))
                              (Prims.of_int (262)) (Prims.of_int (46)))))
                     (Obj.magic uu___1)
                     (fun uu___2 ->
                        (fun ty' ->
                           let uu___2 =
                             FStarC_Tactics_V1_Builtins.inspect ty' in
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.InteractiveHelpers.ExploreTerm.fst"
                                         (Prims.of_int (258))
                                         (Prims.of_int (14))
                                         (Prims.of_int (258))
                                         (Prims.of_int (25)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.InteractiveHelpers.ExploreTerm.fst"
                                         (Prims.of_int (258))
                                         (Prims.of_int (8))
                                         (Prims.of_int (262))
                                         (Prims.of_int (46)))))
                                (Obj.magic uu___2)
                                (fun uu___3 ->
                                   (fun uu___3 ->
                                      match uu___3 with
                                      | FStarC_Reflection_V1_Data.Tv_Arrow
                                          (b1, c1) ->
                                          Obj.magic
                                            (subst_binder_in_comp e b1 t c1)
                                      | uu___4 ->
                                          Obj.magic
                                            (FStar_InteractiveHelpers_Base.mfail
                                               "inst_comp_once: inconsistent state"))
                                     uu___3))) uu___2))) uu___1)
let rec (inst_comp :
  FStarC_Reflection_Types.env ->
    FStarC_Reflection_Types.comp ->
      FStarC_Reflection_Types.term Prims.list ->
        (FStarC_Reflection_Types.comp, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun e ->
           fun c ->
             fun tl ->
               match tl with
               | [] ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> c)))
               | t::tl' ->
                   Obj.magic
                     (Obj.repr
                        (let uu___ =
                           FStar_Tactics_V1_Derived.try_with
                             (fun uu___1 ->
                                match () with | () -> inst_comp_once e c t)
                             (fun uu___1 ->
                                (fun uu___1 ->
                                   match uu___1 with
                                   | FStar_InteractiveHelpers_Base.MetaAnalysis
                                       msg ->
                                       Obj.magic
                                         (Obj.repr
                                            (FStar_InteractiveHelpers_Base.mfail_doc
                                               (FStar_List_Tot_Base.op_At
                                                  [FStarC_Pprint.arbitrary_string
                                                     "inst_comp: error"] msg)))
                                   | err ->
                                       Obj.magic
                                         (Obj.repr
                                            (FStar_Tactics_Effect.raise err)))
                                  uu___1) in
                         FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                    (Prims.of_int (270)) (Prims.of_int (13))
                                    (Prims.of_int (272)) (Prims.of_int (36)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                    (Prims.of_int (274)) (Prims.of_int (4))
                                    (Prims.of_int (274)) (Prims.of_int (22)))))
                           (Obj.magic uu___)
                           (fun uu___1 ->
                              (fun c' -> Obj.magic (inst_comp e c' tl'))
                                uu___1)))) uu___2 uu___1 uu___
let (_abs_update_typ :
  FStarC_Reflection_Types.binder ->
    FStarC_Reflection_Types.typ ->
      FStarC_Reflection_Types.binder Prims.list ->
        FStarC_Reflection_Types.env ->
          (typ_or_comp, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun b ->
    fun ty ->
      fun pl ->
        fun e ->
          FStar_Tactics_V1_Derived.try_with
            (fun uu___ ->
               match () with
               | () ->
                   let uu___1 = unfold_until_arrow e ty in
                   FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.InteractiveHelpers.ExploreTerm.fst"
                              (Prims.of_int (289)) (Prims.of_int (14))
                              (Prims.of_int (289)) (Prims.of_int (37)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.InteractiveHelpers.ExploreTerm.fst"
                              (Prims.of_int (290)) (Prims.of_int (10))
                              (Prims.of_int (295)) (Prims.of_int (49)))))
                     (Obj.magic uu___1)
                     (fun uu___2 ->
                        (fun ty' ->
                           let uu___2 =
                             FStarC_Tactics_V1_Builtins.inspect ty' in
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.InteractiveHelpers.ExploreTerm.fst"
                                         (Prims.of_int (290))
                                         (Prims.of_int (16))
                                         (Prims.of_int (290))
                                         (Prims.of_int (27)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.InteractiveHelpers.ExploreTerm.fst"
                                         (Prims.of_int (290))
                                         (Prims.of_int (10))
                                         (Prims.of_int (295))
                                         (Prims.of_int (49)))))
                                (Obj.magic uu___2)
                                (fun uu___3 ->
                                   (fun uu___3 ->
                                      match uu___3 with
                                      | FStarC_Reflection_V1_Data.Tv_Arrow
                                          (b1, c1) ->
                                          let uu___4 =
                                            let uu___5 =
                                              FStarC_Tactics_V1_Builtins.pack
                                                (FStarC_Reflection_V1_Data.Tv_Var
                                                   (FStar_Reflection_V1_Derived.bv_of_binder
                                                      b)) in
                                            FStar_Tactics_Effect.tac_bind
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                       (Prims.of_int (292))
                                                       (Prims.of_int (42))
                                                       (Prims.of_int (292))
                                                       (Prims.of_int (74)))))
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                       (Prims.of_int (292))
                                                       (Prims.of_int (16))
                                                       (Prims.of_int (292))
                                                       (Prims.of_int (77)))))
                                              (Obj.magic uu___5)
                                              (fun uu___6 ->
                                                 (fun uu___6 ->
                                                    Obj.magic
                                                      (subst_binder_in_comp e
                                                         b1 uu___6 c1))
                                                   uu___6) in
                                          Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                        (Prims.of_int (292))
                                                        (Prims.of_int (16))
                                                        (Prims.of_int (292))
                                                        (Prims.of_int (77)))))
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                        (Prims.of_int (293))
                                                        (Prims.of_int (6))
                                                        (Prims.of_int (293))
                                                        (Prims.of_int (29)))))
                                               (Obj.magic uu___4)
                                               (fun c1' ->
                                                  FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___5 ->
                                                       TC_Comp
                                                         (c1', (b :: pl),
                                                           Prims.int_zero))))
                                      | uu___4 ->
                                          Obj.magic
                                            (FStar_InteractiveHelpers_Base.mfail
                                               "_abs_update_typ: inconsistent state"))
                                     uu___3))) uu___2))
            (fun uu___ ->
               (fun uu___ ->
                  match uu___ with
                  | FStar_InteractiveHelpers_Base.MetaAnalysis msg ->
                      Obj.magic
                        (Obj.repr
                           (let uu___1 =
                              let uu___2 =
                                let uu___3 =
                                  let uu___4 =
                                    let uu___5 =
                                      FStarC_Tactics_V1_Builtins.term_to_string
                                        ty in
                                    FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "FStar.InteractiveHelpers.ExploreTerm.fst"
                                               (Prims.of_int (300))
                                               (Prims.of_int (62))
                                               (Prims.of_int (300))
                                               (Prims.of_int (79)))))
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
                                              Prims.strcat
                                                "_abs_update_typ: could not find an arrow in "
                                                uu___6)) in
                                  FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.InteractiveHelpers.ExploreTerm.fst"
                                             (Prims.of_int (300))
                                             (Prims.of_int (12))
                                             (Prims.of_int (300))
                                             (Prims.of_int (80)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.InteractiveHelpers.ExploreTerm.fst"
                                             (Prims.of_int (300))
                                             (Prims.of_int (7))
                                             (Prims.of_int (300))
                                             (Prims.of_int (80)))))
                                    (Obj.magic uu___4)
                                    (fun uu___5 ->
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___6 ->
                                            FStarC_Errors_Msg.text uu___5)) in
                                FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "FStar.InteractiveHelpers.ExploreTerm.fst"
                                           (Prims.of_int (300))
                                           (Prims.of_int (7))
                                           (Prims.of_int (300))
                                           (Prims.of_int (80)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "FStar.InteractiveHelpers.ExploreTerm.fst"
                                           (Prims.of_int (300))
                                           (Prims.of_int (6))
                                           (Prims.of_int (300))
                                           (Prims.of_int (81)))))
                                  (Obj.magic uu___3)
                                  (fun uu___4 ->
                                     FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___5 -> [uu___4])) in
                              FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.InteractiveHelpers.ExploreTerm.fst"
                                         (Prims.of_int (300))
                                         (Prims.of_int (6))
                                         (Prims.of_int (300))
                                         (Prims.of_int (81)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.InteractiveHelpers.ExploreTerm.fst"
                                         (Prims.of_int (299))
                                         (Prims.of_int (14))
                                         (Prims.of_int (302))
                                         (Prims.of_int (5)))))
                                (Obj.magic uu___2)
                                (fun uu___3 ->
                                   FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___4 ->
                                        FStar_List_Tot_Base.op_At uu___3 msg)) in
                            FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "FStar.InteractiveHelpers.ExploreTerm.fst"
                                       (Prims.of_int (299))
                                       (Prims.of_int (14))
                                       (Prims.of_int (302))
                                       (Prims.of_int (5)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "FStar.InteractiveHelpers.ExploreTerm.fst"
                                       (Prims.of_int (299))
                                       (Prims.of_int (4))
                                       (Prims.of_int (302))
                                       (Prims.of_int (5)))))
                              (Obj.magic uu___1)
                              (fun uu___2 ->
                                 (fun uu___2 ->
                                    Obj.magic
                                      (FStar_InteractiveHelpers_Base.mfail_doc
                                         uu___2)) uu___2)))
                  | err ->
                      Obj.magic (Obj.repr (FStar_Tactics_Effect.raise err)))
                 uu___)
let (abs_update_typ_or_comp :
  FStarC_Reflection_Types.binder ->
    typ_or_comp ->
      FStarC_Reflection_Types.env ->
        (typ_or_comp, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun b ->
           fun c ->
             fun e ->
               Obj.magic
                 (FStar_Tactics_Effect.lift_div_tac
                    (fun uu___ ->
                       match c with
                       | TC_Typ (v, pl, n) ->
                           TC_Typ (v, (b :: pl), (n + Prims.int_one))
                       | TC_Comp (v, pl, n) ->
                           TC_Comp (v, (b :: pl), (n + Prims.int_one)))))
          uu___2 uu___1 uu___
let (abs_update_opt_typ_or_comp :
  FStarC_Reflection_Types.binder ->
    typ_or_comp FStar_Pervasives_Native.option ->
      FStarC_Reflection_Types.env ->
        (typ_or_comp FStar_Pervasives_Native.option, unit)
          FStar_Tactics_Effect.tac_repr)
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun b ->
           fun opt_c ->
             fun e ->
               match opt_c with
               | FStar_Pervasives_Native.None ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.lift_div_tac
                           (fun uu___ -> FStar_Pervasives_Native.None)))
               | FStar_Pervasives_Native.Some c ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_V1_Derived.try_with
                           (fun uu___ ->
                              match () with
                              | () ->
                                  let uu___1 = abs_update_typ_or_comp b c e in
                                  FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.InteractiveHelpers.ExploreTerm.fst"
                                             (Prims.of_int (324))
                                             (Prims.of_int (14))
                                             (Prims.of_int (324))
                                             (Prims.of_int (42)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.InteractiveHelpers.ExploreTerm.fst"
                                             (Prims.of_int (325))
                                             (Prims.of_int (6))
                                             (Prims.of_int (325))
                                             (Prims.of_int (12)))))
                                    (Obj.magic uu___1)
                                    (fun c1 ->
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___2 ->
                                            FStar_Pervasives_Native.Some c1)))
                           (fun uu___ ->
                              (fun uu___ ->
                                 match uu___ with
                                 | FStar_InteractiveHelpers_Base.MetaAnalysis
                                     msg ->
                                     Obj.magic
                                       (FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___1 ->
                                             FStar_Pervasives_Native.None))
                                 | err ->
                                     Obj.magic
                                       (FStar_Tactics_Effect.raise err))
                                uu___)))) uu___2 uu___1 uu___
let rec (_flush_typ_or_comp_comp :
  Prims.bool ->
    FStarC_Reflection_Types.env ->
      FStarC_Reflection_Types.binder Prims.list ->
        ((FStarC_Reflection_Types.bv * FStarC_Reflection_Types.typ) *
          FStarC_Reflection_Types.term) Prims.list ->
          FStarC_Reflection_Types.comp ->
            (FStarC_Reflection_Types.comp, unit)
              FStar_Tactics_Effect.tac_repr)
  =
  fun dbg ->
    fun e ->
      fun rem ->
        fun inst ->
          fun c ->
            let uu___ =
              Obj.magic
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___1 ->
                      fun c1 ->
                        fun inst1 ->
                          let uu___2 =
                            Obj.magic
                              (FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___3 -> FStar_List_Tot_Base.rev inst1)) in
                          FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.InteractiveHelpers.ExploreTerm.fst"
                                     (Prims.of_int (342)) (Prims.of_int (15))
                                     (Prims.of_int (342)) (Prims.of_int (32)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.InteractiveHelpers.ExploreTerm.fst"
                                     (Prims.of_int (343)) (Prims.of_int (4))
                                     (Prims.of_int (343)) (Prims.of_int (32)))))
                            (Obj.magic uu___2)
                            (fun uu___3 ->
                               (fun inst2 ->
                                  Obj.magic
                                    (FStar_InteractiveHelpers_Base.apply_subst_in_comp
                                       e c1 inst2)) uu___3))) in
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range
                       "FStar.InteractiveHelpers.ExploreTerm.fst"
                       (Prims.of_int (341)) (Prims.of_int (20))
                       (Prims.of_int (343)) (Prims.of_int (32)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range
                       "FStar.InteractiveHelpers.ExploreTerm.fst"
                       (Prims.of_int (345)) (Prims.of_int (2))
                       (Prims.of_int (362)) (Prims.of_int (86)))))
              (Obj.magic uu___)
              (fun uu___1 ->
                 (fun flush ->
                    match rem with
                    | [] -> Obj.magic (flush c inst)
                    | b::rem' ->
                        let uu___1 =
                          Obj.magic
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___2 -> get_comp_ret_type c)) in
                        Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "FStar.InteractiveHelpers.ExploreTerm.fst"
                                      (Prims.of_int (351))
                                      (Prims.of_int (13))
                                      (Prims.of_int (351))
                                      (Prims.of_int (32)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "FStar.InteractiveHelpers.ExploreTerm.fst"
                                      (Prims.of_int (351))
                                      (Prims.of_int (35))
                                      (Prims.of_int (362))
                                      (Prims.of_int (86)))))
                             (Obj.magic uu___1)
                             (fun uu___2 ->
                                (fun ty ->
                                   let uu___2 =
                                     let uu___3 =
                                       let uu___4 =
                                         FStarC_Tactics_V1_Builtins.inspect
                                           ty in
                                       FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                  (Prims.of_int (353))
                                                  (Prims.of_int (19))
                                                  (Prims.of_int (353))
                                                  (Prims.of_int (31)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                  (Prims.of_int (353))
                                                  (Prims.of_int (9))
                                                  (Prims.of_int (353))
                                                  (Prims.of_int (31)))))
                                         (Obj.magic uu___4)
                                         (fun uu___5 ->
                                            FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___6 ->
                                                 FStarC_Reflection_V1_Data.uu___is_Tv_Arrow
                                                   uu___5)) in
                                     FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                (Prims.of_int (353))
                                                (Prims.of_int (9))
                                                (Prims.of_int (353))
                                                (Prims.of_int (31)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                (Prims.of_int (353))
                                                (Prims.of_int (6))
                                                (Prims.of_int (354))
                                                (Prims.of_int (47)))))
                                       (Obj.magic uu___3)
                                       (fun uu___4 ->
                                          (fun uu___4 ->
                                             if uu___4
                                             then
                                               Obj.magic
                                                 (Obj.repr
                                                    (FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___5 ->
                                                          (ty, inst))))
                                             else
                                               Obj.magic
                                                 (Obj.repr
                                                    (let uu___6 =
                                                       let uu___7 =
                                                         flush c inst in
                                                       FStar_Tactics_Effect.tac_bind
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                  (Prims.of_int (354))
                                                                  (Prims.of_int (29))
                                                                  (Prims.of_int (354))
                                                                  (Prims.of_int (43)))))
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                  (Prims.of_int (354))
                                                                  (Prims.of_int (11))
                                                                  (Prims.of_int (354))
                                                                  (Prims.of_int (43)))))
                                                         (Obj.magic uu___7)
                                                         (fun uu___8 ->
                                                            FStar_Tactics_Effect.lift_div_tac
                                                              (fun uu___9 ->
                                                                 get_comp_ret_type
                                                                   uu___8)) in
                                                     FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                (Prims.of_int (354))
                                                                (Prims.of_int (11))
                                                                (Prims.of_int (354))
                                                                (Prims.of_int (43)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                (Prims.of_int (354))
                                                                (Prims.of_int (11))
                                                                (Prims.of_int (354))
                                                                (Prims.of_int (47)))))
                                                       (Obj.magic uu___6)
                                                       (fun uu___7 ->
                                                          FStar_Tactics_Effect.lift_div_tac
                                                            (fun uu___8 ->
                                                               (uu___7, []))))))
                                            uu___4) in
                                   Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                 (Prims.of_int (353))
                                                 (Prims.of_int (6))
                                                 (Prims.of_int (354))
                                                 (Prims.of_int (47)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                 (Prims.of_int (351))
                                                 (Prims.of_int (35))
                                                 (Prims.of_int (362))
                                                 (Prims.of_int (86)))))
                                        (Obj.magic uu___2)
                                        (fun uu___3 ->
                                           (fun uu___3 ->
                                              match uu___3 with
                                              | (ty1, inst') ->
                                                  let uu___4 =
                                                    FStarC_Tactics_V1_Builtins.inspect
                                                      ty1 in
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                (Prims.of_int (356))
                                                                (Prims.of_int (10))
                                                                (Prims.of_int (356))
                                                                (Prims.of_int (20)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                (Prims.of_int (356))
                                                                (Prims.of_int (4))
                                                                (Prims.of_int (362))
                                                                (Prims.of_int (86)))))
                                                       (Obj.magic uu___4)
                                                       (fun uu___5 ->
                                                          (fun uu___5 ->
                                                             match uu___5
                                                             with
                                                             | FStarC_Reflection_V1_Data.Tv_Arrow
                                                                 (b', c') ->
                                                                 let uu___6 =
                                                                   let uu___7
                                                                    =
                                                                    let uu___8
                                                                    =
                                                                    let uu___9
                                                                    =
                                                                    FStar_Tactics_V1_Derived.binder_sort
                                                                    b' in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (358))
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (358))
                                                                    (Prims.of_int (75)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (358))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (358))
                                                                    (Prims.of_int (76)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    ((FStar_Reflection_V1_Derived.bv_of_binder
                                                                    b'),
                                                                    uu___10))) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (358))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (358))
                                                                    (Prims.of_int (76)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (358))
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (358))
                                                                    (Prims.of_int (109)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    let uu___10
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.pack
                                                                    (FStarC_Reflection_V1_Data.Tv_Var
                                                                    (FStar_Reflection_V1_Derived.bv_of_binder
                                                                    b)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (358))
                                                                    (Prims.of_int (78))
                                                                    (Prims.of_int (358))
                                                                    (Prims.of_int (108)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (358))
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (358))
                                                                    (Prims.of_int (109)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (uu___9,
                                                                    uu___11)))))
                                                                    uu___9) in
                                                                   FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (358))
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (358))
                                                                    (Prims.of_int (109)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (358))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (358))
                                                                    (Prims.of_int (116)))))
                                                                    (Obj.magic
                                                                    uu___7)
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    uu___8 ::
                                                                    inst)) in
                                                                 Obj.magic
                                                                   (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (358))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (358))
                                                                    (Prims.of_int (116)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (358))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (358))
                                                                    (Prims.of_int (119)))))
                                                                    (Obj.magic
                                                                    uu___6)
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    Obj.magic
                                                                    (_flush_typ_or_comp_comp
                                                                    dbg e
                                                                    rem'
                                                                    uu___7 c'))
                                                                    uu___7))
                                                             | uu___6 ->
                                                                 let uu___7 =
                                                                   let uu___8
                                                                    =
                                                                    let uu___9
                                                                    =
                                                                    let uu___10
                                                                    =
                                                                    FStar_InteractiveHelpers_Base.acomp_to_string
                                                                    c in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (361))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (361))
                                                                    (Prims.of_int (44)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (361))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (362))
                                                                    (Prims.of_int (85)))))
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
                                                                    FStar_InteractiveHelpers_Base.list_to_string
                                                                    (fun b1
                                                                    ->
                                                                    FStar_Tactics_V1_Derived.name_of_binder
                                                                    b1) rem in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (362))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (362))
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
                                                                    uu___13)
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    Prims.strcat
                                                                    "\n-remaning binders: "
                                                                    uu___14)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (362))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (362))
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
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    Prims.strcat
                                                                    uu___11
                                                                    uu___13))))
                                                                    uu___11) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (361))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (362))
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
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    Prims.strcat
                                                                    "\n-comp: "
                                                                    uu___10)) in
                                                                   FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (361))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (362))
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
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    Prims.strcat
                                                                    "_flush_typ_or_comp: inconsistent state"
                                                                    uu___9)) in
                                                                 Obj.magic
                                                                   (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (360))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (362))
                                                                    (Prims.of_int (86)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (360))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (362))
                                                                    (Prims.of_int (86)))))
                                                                    (Obj.magic
                                                                    uu___7)
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.mfail
                                                                    uu___8))
                                                                    uu___8)))
                                                            uu___5))) uu___3)))
                                  uu___2))) uu___1)
let (flush_typ_or_comp :
  Prims.bool ->
    FStarC_Reflection_Types.env ->
      typ_or_comp -> (typ_or_comp, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun dbg ->
    fun e ->
      fun tyc ->
        let uu___ =
          Obj.magic
            (FStar_Tactics_Effect.lift_div_tac
               (fun uu___1 ->
                  fun pl ->
                    fun n ->
                      fun c ->
                        let uu___2 =
                          Obj.magic
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___3 ->
                                  FStar_List_Tot_Base.splitAt n pl)) in
                        FStar_Tactics_Effect.tac_bind
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "FStar.InteractiveHelpers.ExploreTerm.fst"
                                   (Prims.of_int (366)) (Prims.of_int (17))
                                   (Prims.of_int (366)) (Prims.of_int (38)))))
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "FStar.InteractiveHelpers.ExploreTerm.fst"
                                   (Prims.of_int (365)) (Prims.of_int (88))
                                   (Prims.of_int (369)) (Prims.of_int (18)))))
                          (Obj.magic uu___2)
                          (fun uu___3 ->
                             (fun uu___3 ->
                                match uu___3 with
                                | (pl', uu___4) ->
                                    let uu___5 =
                                      Obj.magic
                                        (FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___6 ->
                                              FStar_List_Tot_Base.rev pl')) in
                                    Obj.magic
                                      (FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                  (Prims.of_int (367))
                                                  (Prims.of_int (14))
                                                  (Prims.of_int (367))
                                                  (Prims.of_int (30)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                  (Prims.of_int (367))
                                                  (Prims.of_int (33))
                                                  (Prims.of_int (369))
                                                  (Prims.of_int (18)))))
                                         (Obj.magic uu___5)
                                         (fun uu___6 ->
                                            (fun pl'1 ->
                                               let uu___6 =
                                                 _flush_typ_or_comp_comp dbg
                                                   e pl'1 [] c in
                                               Obj.magic
                                                 (FStar_Tactics_Effect.tac_bind
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                             (Prims.of_int (368))
                                                             (Prims.of_int (12))
                                                             (Prims.of_int (368))
                                                             (Prims.of_int (50)))))
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                             (Prims.of_int (369))
                                                             (Prims.of_int (4))
                                                             (Prims.of_int (369))
                                                             (Prims.of_int (18)))))
                                                    (Obj.magic uu___6)
                                                    (fun c1 ->
                                                       FStar_Tactics_Effect.lift_div_tac
                                                         (fun uu___7 ->
                                                            TC_Comp
                                                              (c1, pl,
                                                                Prims.int_zero)))))
                                              uu___6))) uu___3))) in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range
                   "FStar.InteractiveHelpers.ExploreTerm.fst"
                   (Prims.of_int (365)) (Prims.of_int (88))
                   (Prims.of_int (369)) (Prims.of_int (18)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range
                   "FStar.InteractiveHelpers.ExploreTerm.fst"
                   (Prims.of_int (371)) (Prims.of_int (2))
                   (Prims.of_int (379)) (Prims.of_int (25)))))
          (Obj.magic uu___)
          (fun uu___1 ->
             (fun flush_comp ->
                Obj.magic
                  (FStar_Tactics_V1_Derived.try_with
                     (fun uu___1 ->
                        match () with
                        | () ->
                            (match tyc with
                             | TC_Typ (ty, pl, n) ->
                                 let uu___2 =
                                   Obj.magic
                                     (FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___3 ->
                                           FStarC_Reflection_V1_Builtins.pack_comp
                                             (FStarC_Reflection_V1_Data.C_Total
                                                ty))) in
                                 FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "FStar.InteractiveHelpers.ExploreTerm.fst"
                                            (Prims.of_int (373))
                                            (Prims.of_int (12))
                                            (Prims.of_int (373))
                                            (Prims.of_int (34)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "FStar.InteractiveHelpers.ExploreTerm.fst"
                                            (Prims.of_int (374))
                                            (Prims.of_int (4))
                                            (Prims.of_int (374))
                                            (Prims.of_int (21)))))
                                   (Obj.magic uu___2)
                                   (fun uu___3 ->
                                      (fun c -> Obj.magic (flush_comp pl n c))
                                        uu___3)
                             | TC_Comp (c, pl, n) -> flush_comp pl n c))
                     (fun uu___1 ->
                        (fun uu___1 ->
                           match uu___1 with
                           | FStar_InteractiveHelpers_Base.MetaAnalysis msg
                               ->
                               Obj.magic
                                 (Obj.repr
                                    (let uu___2 =
                                       let uu___3 =
                                         let uu___4 =
                                           let uu___5 =
                                             let uu___6 =
                                               typ_or_comp_to_string tyc in
                                             FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                        (Prims.of_int (378))
                                                        (Prims.of_int (61))
                                                        (Prims.of_int (378))
                                                        (Prims.of_int (86)))))
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
                                                         "flush_typ_or_comp failed on: "
                                                         uu___7)) in
                                           FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                      (Prims.of_int (378))
                                                      (Prims.of_int (26))
                                                      (Prims.of_int (378))
                                                      (Prims.of_int (87)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                      (Prims.of_int (378))
                                                      (Prims.of_int (21))
                                                      (Prims.of_int (378))
                                                      (Prims.of_int (87)))))
                                             (Obj.magic uu___5)
                                             (fun uu___6 ->
                                                FStar_Tactics_Effect.lift_div_tac
                                                  (fun uu___7 ->
                                                     FStarC_Errors_Msg.text
                                                       uu___6)) in
                                         FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                    (Prims.of_int (378))
                                                    (Prims.of_int (21))
                                                    (Prims.of_int (378))
                                                    (Prims.of_int (87)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                    (Prims.of_int (378))
                                                    (Prims.of_int (20))
                                                    (Prims.of_int (378))
                                                    (Prims.of_int (88)))))
                                           (Obj.magic uu___4)
                                           (fun uu___5 ->
                                              FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___6 -> [uu___5])) in
                                       FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                  (Prims.of_int (378))
                                                  (Prims.of_int (20))
                                                  (Prims.of_int (378))
                                                  (Prims.of_int (88)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                  (Prims.of_int (378))
                                                  (Prims.of_int (19))
                                                  (Prims.of_int (378))
                                                  (Prims.of_int (96)))))
                                         (Obj.magic uu___3)
                                         (fun uu___4 ->
                                            FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___5 ->
                                                 FStar_List_Tot_Base.op_At
                                                   uu___4 msg)) in
                                     FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                (Prims.of_int (378))
                                                (Prims.of_int (19))
                                                (Prims.of_int (378))
                                                (Prims.of_int (96)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                (Prims.of_int (378))
                                                (Prims.of_int (9))
                                                (Prims.of_int (378))
                                                (Prims.of_int (96)))))
                                       (Obj.magic uu___2)
                                       (fun uu___3 ->
                                          (fun uu___3 ->
                                             Obj.magic
                                               (FStar_InteractiveHelpers_Base.mfail_doc
                                                  uu___3)) uu___3)))
                           | err ->
                               Obj.magic
                                 (Obj.repr (FStar_Tactics_Effect.raise err)))
                          uu___1))) uu___1)
let (safe_arg_typ_or_comp :
  Prims.bool ->
    FStarC_Reflection_Types.env ->
      FStarC_Reflection_Types.term ->
        (typ_or_comp FStar_Pervasives_Native.option, unit)
          FStar_Tactics_Effect.tac_repr)
  =
  fun dbg ->
    fun e ->
      fun hd ->
        let uu___ =
          let uu___1 =
            let uu___2 = FStarC_Tactics_V1_Builtins.term_to_string hd in
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range
                       "FStar.InteractiveHelpers.ExploreTerm.fst"
                       (Prims.of_int (386)) (Prims.of_int (44))
                       (Prims.of_int (386)) (Prims.of_int (61)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Prims.fst" (Prims.of_int (611))
                       (Prims.of_int (19)) (Prims.of_int (611))
                       (Prims.of_int (31))))) (Obj.magic uu___2)
              (fun uu___3 ->
                 FStar_Tactics_Effect.lift_div_tac
                   (fun uu___4 ->
                      Prims.strcat "safe_arg_typ_or_comp: " uu___3)) in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range
                     "FStar.InteractiveHelpers.ExploreTerm.fst"
                     (Prims.of_int (386)) (Prims.of_int (16))
                     (Prims.of_int (386)) (Prims.of_int (62)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range
                     "FStar.InteractiveHelpers.ExploreTerm.fst"
                     (Prims.of_int (386)) (Prims.of_int (2))
                     (Prims.of_int (386)) (Prims.of_int (62)))))
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
                   "FStar.InteractiveHelpers.ExploreTerm.fst"
                   (Prims.of_int (386)) (Prims.of_int (2))
                   (Prims.of_int (386)) (Prims.of_int (62)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range
                   "FStar.InteractiveHelpers.ExploreTerm.fst"
                   (Prims.of_int (387)) (Prims.of_int (2))
                   (Prims.of_int (407)) (Prims.of_int (15)))))
          (Obj.magic uu___)
          (fun uu___1 ->
             (fun uu___1 ->
                let uu___2 = safe_tc e hd in
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.InteractiveHelpers.ExploreTerm.fst"
                              (Prims.of_int (387)) (Prims.of_int (8))
                              (Prims.of_int (387)) (Prims.of_int (20)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.InteractiveHelpers.ExploreTerm.fst"
                              (Prims.of_int (387)) (Prims.of_int (2))
                              (Prims.of_int (407)) (Prims.of_int (15)))))
                     (Obj.magic uu___2)
                     (fun uu___3 ->
                        (fun uu___3 ->
                           match uu___3 with
                           | FStar_Pervasives_Native.None ->
                               Obj.magic
                                 (Obj.repr
                                    (FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___4 ->
                                          FStar_Pervasives_Native.None)))
                           | FStar_Pervasives_Native.Some ty ->
                               Obj.magic
                                 (Obj.repr
                                    (let uu___4 =
                                       let uu___5 =
                                         let uu___6 =
                                           FStarC_Tactics_V1_Builtins.term_to_string
                                             ty in
                                         FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                    (Prims.of_int (390))
                                                    (Prims.of_int (33))
                                                    (Prims.of_int (390))
                                                    (Prims.of_int (50)))))
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
                                                   Prims.strcat "hd type: "
                                                     uu___7)) in
                                       FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                  (Prims.of_int (390))
                                                  (Prims.of_int (18))
                                                  (Prims.of_int (390))
                                                  (Prims.of_int (51)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                  (Prims.of_int (390))
                                                  (Prims.of_int (4))
                                                  (Prims.of_int (390))
                                                  (Prims.of_int (51)))))
                                         (Obj.magic uu___5)
                                         (fun uu___6 ->
                                            (fun uu___6 ->
                                               Obj.magic
                                                 (FStar_InteractiveHelpers_Base.print_dbg
                                                    dbg uu___6)) uu___6) in
                                     FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                (Prims.of_int (390))
                                                (Prims.of_int (4))
                                                (Prims.of_int (390))
                                                (Prims.of_int (51)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                (Prims.of_int (390))
                                                (Prims.of_int (52))
                                                (Prims.of_int (407))
                                                (Prims.of_int (15)))))
                                       (Obj.magic uu___4)
                                       (fun uu___5 ->
                                          (fun uu___5 ->
                                             let uu___6 =
                                               let uu___7 =
                                                 let uu___8 =
                                                   FStarC_Tactics_V1_Builtins.inspect
                                                     ty in
                                                 FStar_Tactics_Effect.tac_bind
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                            (Prims.of_int (392))
                                                            (Prims.of_int (19))
                                                            (Prims.of_int (392))
                                                            (Prims.of_int (31)))))
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                            (Prims.of_int (392))
                                                            (Prims.of_int (9))
                                                            (Prims.of_int (392))
                                                            (Prims.of_int (31)))))
                                                   (Obj.magic uu___8)
                                                   (fun uu___9 ->
                                                      FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___10 ->
                                                           FStarC_Reflection_V1_Data.uu___is_Tv_Arrow
                                                             uu___9)) in
                                               FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                          (Prims.of_int (392))
                                                          (Prims.of_int (9))
                                                          (Prims.of_int (392))
                                                          (Prims.of_int (31)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                          (Prims.of_int (392))
                                                          (Prims.of_int (6))
                                                          (Prims.of_int (403))
                                                          (Prims.of_int (11)))))
                                                 (Obj.magic uu___7)
                                                 (fun uu___8 ->
                                                    (fun uu___8 ->
                                                       if uu___8
                                                       then
                                                         let uu___9 =
                                                           FStar_InteractiveHelpers_Base.print_dbg
                                                             dbg
                                                             "no need to unfold the type" in
                                                         Obj.magic
                                                           (FStar_Tactics_Effect.tac_bind
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (394))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (394))
                                                                    (Prims.of_int (50)))))
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (389))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (389))
                                                                    (Prims.of_int (11)))))
                                                              (Obj.magic
                                                                 uu___9)
                                                              (fun uu___10 ->
                                                                 FStar_Tactics_Effect.lift_div_tac
                                                                   (fun
                                                                    uu___11
                                                                    -> ty)))
                                                       else
                                                         (let uu___10 =
                                                            FStar_InteractiveHelpers_Base.print_dbg
                                                              dbg
                                                              "need to unfold the type" in
                                                          Obj.magic
                                                            (FStar_Tactics_Effect.tac_bind
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (399))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (399))
                                                                    (Prims.of_int (47)))))
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (399))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (402))
                                                                    (Prims.of_int (10)))))
                                                               (Obj.magic
                                                                  uu___10)
                                                               (fun uu___11
                                                                  ->
                                                                  (fun
                                                                    uu___11
                                                                    ->
                                                                    let uu___12
                                                                    =
                                                                    unfold_until_arrow
                                                                    e ty in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (400))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (400))
                                                                    (Prims.of_int (40)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (401))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (402))
                                                                    (Prims.of_int (10)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (fun ty1
                                                                    ->
                                                                    let uu___13
                                                                    =
                                                                    let uu___14
                                                                    =
                                                                    let uu___15
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.term_to_string
                                                                    ty1 in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (401))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (401))
                                                                    (Prims.of_int (66)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___15)
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    Prims.strcat
                                                                    "result of unfolding : "
                                                                    uu___16)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (401))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (401))
                                                                    (Prims.of_int (67)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (401))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (401))
                                                                    (Prims.of_int (67)))))
                                                                    (Obj.magic
                                                                    uu___14)
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
                                                                    uu___15) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (401))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (401))
                                                                    (Prims.of_int (67)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (400))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (400))
                                                                    (Prims.of_int (14)))))
                                                                    (Obj.magic
                                                                    uu___13)
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___15
                                                                    -> ty1))))
                                                                    uu___13)))
                                                                    uu___11))))
                                                      uu___8) in
                                             Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                           (Prims.of_int (392))
                                                           (Prims.of_int (6))
                                                           (Prims.of_int (403))
                                                           (Prims.of_int (11)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                           (Prims.of_int (405))
                                                           (Prims.of_int (4))
                                                           (Prims.of_int (407))
                                                           (Prims.of_int (15)))))
                                                  (Obj.magic uu___6)
                                                  (fun uu___7 ->
                                                     (fun ty1 ->
                                                        let uu___7 =
                                                          FStarC_Tactics_V1_Builtins.inspect
                                                            ty1 in
                                                        Obj.magic
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (405))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (405))
                                                                    (Prims.of_int (20)))))
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (405))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (407))
                                                                    (Prims.of_int (15)))))
                                                             (Obj.magic
                                                                uu___7)
                                                             (fun uu___8 ->
                                                                FStar_Tactics_Effect.lift_div_tac
                                                                  (fun uu___9
                                                                    ->
                                                                    match uu___8
                                                                    with
                                                                    | 
                                                                    FStarC_Reflection_V1_Data.Tv_Arrow
                                                                    (b, c) ->
                                                                    FStar_Pervasives_Native.Some
                                                                    (TC_Typ
                                                                    ((FStar_Reflection_V1_Derived.type_of_binder
                                                                    b), [],
                                                                    Prims.int_zero))
                                                                    | 
                                                                    uu___10
                                                                    ->
                                                                    FStar_Pervasives_Native.None))))
                                                       uu___7))) uu___5))))
                          uu___3))) uu___1)
let (convert_ctrl_flag :
  FStarC_Tactics_Types.ctrl_flag -> FStarC_Tactics_Types.ctrl_flag) =
  fun flag ->
    match flag with
    | FStarC_Tactics_Types.Continue -> FStarC_Tactics_Types.Continue
    | FStarC_Tactics_Types.Skip -> FStarC_Tactics_Types.Continue
    | FStarC_Tactics_Types.Abort -> FStarC_Tactics_Types.Abort
type 'a explorer =
  'a ->
    FStar_InteractiveHelpers_Base.genv ->
      (FStar_InteractiveHelpers_Base.genv *
        FStarC_Reflection_V1_Data.term_view) Prims.list ->
        typ_or_comp FStar_Pervasives_Native.option ->
          FStarC_Reflection_V1_Data.term_view ->
            (('a * FStarC_Tactics_Types.ctrl_flag), unit)
              FStar_Tactics_Effect.tac_repr
let bind_expl :
  'a .
    'a ->
      ('a ->
         (('a * FStarC_Tactics_Types.ctrl_flag), unit)
           FStar_Tactics_Effect.tac_repr)
        ->
        ('a ->
           (('a * FStarC_Tactics_Types.ctrl_flag), unit)
             FStar_Tactics_Effect.tac_repr)
          ->
          (('a * FStarC_Tactics_Types.ctrl_flag), unit)
            FStar_Tactics_Effect.tac_repr
  =
  fun x ->
    fun f1 ->
      fun f2 ->
        let uu___ = f1 x in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range
                   "FStar.InteractiveHelpers.ExploreTerm.fst"
                   (Prims.of_int (438)) (Prims.of_int (18))
                   (Prims.of_int (438)) (Prims.of_int (22)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range
                   "FStar.InteractiveHelpers.ExploreTerm.fst"
                   (Prims.of_int (437)) (Prims.of_int (92))
                   (Prims.of_int (441)) (Prims.of_int (34)))))
          (Obj.magic uu___)
          (fun uu___1 ->
             (fun uu___1 ->
                match uu___1 with
                | (x1, flag1) ->
                    if flag1 = FStarC_Tactics_Types.Continue
                    then Obj.magic (Obj.repr (f2 x1))
                    else
                      Obj.magic
                        (Obj.repr
                           (FStar_Tactics_Effect.lift_div_tac
                              (fun uu___3 -> (x1, (convert_ctrl_flag flag1))))))
               uu___1)
let rec (explore_term :
  Prims.bool ->
    Prims.bool ->
      unit ->
        Obj.t explorer ->
          Obj.t ->
            FStar_InteractiveHelpers_Base.genv ->
              (FStar_InteractiveHelpers_Base.genv *
                FStarC_Reflection_V1_Data.term_view) Prims.list ->
                typ_or_comp FStar_Pervasives_Native.option ->
                  FStarC_Reflection_Types.term ->
                    ((Obj.t * FStarC_Tactics_Types.ctrl_flag), unit)
                      FStar_Tactics_Effect.tac_repr)
  =
  fun dbg ->
    fun dfs ->
      fun a ->
        fun f ->
          fun x ->
            fun ge0 ->
              fun pl0 ->
                fun c0 ->
                  fun t0 ->
                    let uu___ =
                      let uu___1 =
                        let uu___2 =
                          let uu___3 =
                            FStar_InteractiveHelpers_Base.term_construct t0 in
                          FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.InteractiveHelpers.ExploreTerm.fst"
                                     (Prims.of_int (470)) (Prims.of_int (39))
                                     (Prims.of_int (470)) (Prims.of_int (56)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.InteractiveHelpers.ExploreTerm.fst"
                                     (Prims.of_int (470)) (Prims.of_int (39))
                                     (Prims.of_int (470)) (Prims.of_int (84)))))
                            (Obj.magic uu___3)
                            (fun uu___4 ->
                               (fun uu___4 ->
                                  let uu___5 =
                                    let uu___6 =
                                      FStarC_Tactics_V1_Builtins.term_to_string
                                        t0 in
                                    FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "FStar.InteractiveHelpers.ExploreTerm.fst"
                                               (Prims.of_int (470))
                                               (Prims.of_int (67))
                                               (Prims.of_int (470))
                                               (Prims.of_int (84)))))
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
                                              Prims.strcat ":\n" uu___7)) in
                                  Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                (Prims.of_int (470))
                                                (Prims.of_int (59))
                                                (Prims.of_int (470))
                                                (Prims.of_int (84)))))
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
                                               Prims.strcat uu___4 uu___6))))
                                 uu___4) in
                        FStar_Tactics_Effect.tac_bind
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "FStar.InteractiveHelpers.ExploreTerm.fst"
                                   (Prims.of_int (470)) (Prims.of_int (39))
                                   (Prims.of_int (470)) (Prims.of_int (84)))))
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range "Prims.fst"
                                   (Prims.of_int (611)) (Prims.of_int (19))
                                   (Prims.of_int (611)) (Prims.of_int (31)))))
                          (Obj.magic uu___2)
                          (fun uu___3 ->
                             FStar_Tactics_Effect.lift_div_tac
                               (fun uu___4 ->
                                  Prims.strcat "[> explore_term: " uu___3)) in
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.InteractiveHelpers.ExploreTerm.fst"
                                 (Prims.of_int (470)) (Prims.of_int (16))
                                 (Prims.of_int (470)) (Prims.of_int (85)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.InteractiveHelpers.ExploreTerm.fst"
                                 (Prims.of_int (470)) (Prims.of_int (2))
                                 (Prims.of_int (470)) (Prims.of_int (85)))))
                        (Obj.magic uu___1)
                        (fun uu___2 ->
                           (fun uu___2 ->
                              Obj.magic
                                (FStar_InteractiveHelpers_Base.print_dbg dbg
                                   uu___2)) uu___2) in
                    FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range
                               "FStar.InteractiveHelpers.ExploreTerm.fst"
                               (Prims.of_int (470)) (Prims.of_int (2))
                               (Prims.of_int (470)) (Prims.of_int (85)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range
                               "FStar.InteractiveHelpers.ExploreTerm.fst"
                               (Prims.of_int (470)) (Prims.of_int (86))
                               (Prims.of_int (550)) (Prims.of_int (33)))))
                      (Obj.magic uu___)
                      (fun uu___1 ->
                         (fun uu___1 ->
                            let uu___2 =
                              FStarC_Tactics_V1_Builtins.inspect t0 in
                            Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "FStar.InteractiveHelpers.ExploreTerm.fst"
                                          (Prims.of_int (471))
                                          (Prims.of_int (12))
                                          (Prims.of_int (471))
                                          (Prims.of_int (22)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "FStar.InteractiveHelpers.ExploreTerm.fst"
                                          (Prims.of_int (471))
                                          (Prims.of_int (25))
                                          (Prims.of_int (550))
                                          (Prims.of_int (33)))))
                                 (Obj.magic uu___2)
                                 (fun uu___3 ->
                                    (fun tv0 ->
                                       let uu___3 = f x ge0 pl0 c0 tv0 in
                                       Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                     (Prims.of_int (472))
                                                     (Prims.of_int (17))
                                                     (Prims.of_int (472))
                                                     (Prims.of_int (35)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                     (Prims.of_int (471))
                                                     (Prims.of_int (25))
                                                     (Prims.of_int (550))
                                                     (Prims.of_int (33)))))
                                            (Obj.magic uu___3)
                                            (fun uu___4 ->
                                               (fun uu___4 ->
                                                  match uu___4 with
                                                  | (x0, flag) ->
                                                      let uu___5 =
                                                        Obj.magic
                                                          (FStar_Tactics_Effect.lift_div_tac
                                                             (fun uu___6 ->
                                                                (ge0, tv0) ::
                                                                pl0)) in
                                                      Obj.magic
                                                        (FStar_Tactics_Effect.tac_bind
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (473))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (473))
                                                                    (Prims.of_int (29)))))
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (474))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (550))
                                                                    (Prims.of_int (33)))))
                                                           (Obj.magic uu___5)
                                                           (fun uu___6 ->
                                                              (fun pl1 ->
                                                                 if
                                                                   flag =
                                                                    FStarC_Tactics_Types.Continue
                                                                 then
                                                                   Obj.magic
                                                                    (Obj.repr
                                                                    (match tv0
                                                                    with
                                                                    | 
                                                                    FStarC_Reflection_V1_Data.Tv_Var
                                                                    uu___6 ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    (x0,
                                                                    FStarC_Tactics_Types.Continue)))
                                                                    | 
                                                                    FStarC_Reflection_V1_Data.Tv_BVar
                                                                    uu___6 ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    (x0,
                                                                    FStarC_Tactics_Types.Continue)))
                                                                    | 
                                                                    FStarC_Reflection_V1_Data.Tv_FVar
                                                                    uu___6 ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    (x0,
                                                                    FStarC_Tactics_Types.Continue)))
                                                                    | 
                                                                    FStarC_Reflection_V1_Data.Tv_App
                                                                    (hd,
                                                                    (a1,
                                                                    qual)) ->
                                                                    Obj.repr
                                                                    (let uu___6
                                                                    =
                                                                    safe_arg_typ_or_comp
                                                                    dbg
                                                                    ge0.FStar_InteractiveHelpers_Base.env
                                                                    hd in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (481))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (481))
                                                                    (Prims.of_int (51)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (482))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (489))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    uu___6)
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun a_c
                                                                    ->
                                                                    let uu___7
                                                                    =
                                                                    let uu___8
                                                                    =
                                                                    let uu___9
                                                                    =
                                                                    FStar_InteractiveHelpers_Base.option_to_string
                                                                    typ_or_comp_to_string
                                                                    a_c in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (483))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (483))
                                                                    (Prims.of_int (63)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    Prims.strcat
                                                                    "Tv_App: updated target typ_or_comp to:\n"
                                                                    uu___10)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (482))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (483))
                                                                    (Prims.of_int (64)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (482))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (483))
                                                                    (Prims.of_int (64)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    uu___9))
                                                                    uu___9) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (482))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (483))
                                                                    (Prims.of_int (64)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (483))
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (489))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    uu___7)
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    let uu___9
                                                                    =
                                                                    explore_term
                                                                    dbg dfs
                                                                    () f x0
                                                                    ge0 pl1
                                                                    a_c a1 in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (484))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (484))
                                                                    (Prims.of_int (61)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (483))
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (489))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    match uu___10
                                                                    with
                                                                    | 
                                                                    (x1,
                                                                    flag1) ->
                                                                    if
                                                                    flag1 =
                                                                    FStarC_Tactics_Types.Continue
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (explore_term
                                                                    dbg dfs
                                                                    () f x1
                                                                    ge0 pl1
                                                                    FStar_Pervasives_Native.None
                                                                    hd))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (x1,
                                                                    (convert_ctrl_flag
                                                                    flag1))))))
                                                                    uu___10)))
                                                                    uu___8)))
                                                                    uu___7))
                                                                    | 
                                                                    FStarC_Reflection_V1_Data.Tv_Abs
                                                                    (br,
                                                                    body) ->
                                                                    Obj.repr
                                                                    (let uu___6
                                                                    =
                                                                    FStar_InteractiveHelpers_Base.genv_push_binder
                                                                    ge0 br
                                                                    false
                                                                    FStar_Pervasives_Native.None in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (491))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (491))
                                                                    (Prims.of_int (50)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (491))
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (493))
                                                                    (Prims.of_int (47)))))
                                                                    (Obj.magic
                                                                    uu___6)
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun ge1
                                                                    ->
                                                                    let uu___7
                                                                    =
                                                                    abs_update_opt_typ_or_comp
                                                                    br c0
                                                                    ge1.FStar_InteractiveHelpers_Base.env in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (492))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (492))
                                                                    (Prims.of_int (55)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (493))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (493))
                                                                    (Prims.of_int (47)))))
                                                                    (Obj.magic
                                                                    uu___7)
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun c1
                                                                    ->
                                                                    Obj.magic
                                                                    (explore_term
                                                                    dbg dfs
                                                                    () f x0
                                                                    ge1 pl1
                                                                    c1 body))
                                                                    uu___8)))
                                                                    uu___7))
                                                                    | 
                                                                    FStarC_Reflection_V1_Data.Tv_Arrow
                                                                    (br, c01)
                                                                    ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    (x0,
                                                                    FStarC_Tactics_Types.Continue)))
                                                                    | 
                                                                    FStarC_Reflection_V1_Data.Tv_Type
                                                                    uu___6 ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    (x0,
                                                                    FStarC_Tactics_Types.Continue)))
                                                                    | 
                                                                    FStarC_Reflection_V1_Data.Tv_Refine
                                                                    (bv,
                                                                    sort,
                                                                    ref) ->
                                                                    Obj.repr
                                                                    (let uu___6
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStarC_Reflection_V1_Builtins.inspect_bv
                                                                    bv)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (497))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (497))
                                                                    (Prims.of_int (29)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (497))
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (502))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    uu___6)
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun bvv
                                                                    ->
                                                                    let uu___7
                                                                    =
                                                                    explore_term
                                                                    dbg dfs
                                                                    () f x0
                                                                    ge0 pl1
                                                                    FStar_Pervasives_Native.None
                                                                    sort in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (498))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (498))
                                                                    (Prims.of_int (65)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (497))
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (502))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    uu___7)
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    match uu___8
                                                                    with
                                                                    | 
                                                                    (x1,
                                                                    flag1) ->
                                                                    if
                                                                    flag1 =
                                                                    FStarC_Tactics_Types.Continue
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___9
                                                                    =
                                                                    FStar_InteractiveHelpers_Base.genv_push_bv
                                                                    ge0 bv
                                                                    sort
                                                                    false
                                                                    FStar_Pervasives_Native.None in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (500))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (500))
                                                                    (Prims.of_int (53)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (501))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (501))
                                                                    (Prims.of_int (50)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun ge1
                                                                    ->
                                                                    Obj.magic
                                                                    (explore_term
                                                                    dbg dfs
                                                                    () f x1
                                                                    ge1 pl1
                                                                    FStar_Pervasives_Native.None
                                                                    ref))
                                                                    uu___10)))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (x1,
                                                                    (convert_ctrl_flag
                                                                    flag1))))))
                                                                    uu___8)))
                                                                    uu___7))
                                                                    | 
                                                                    FStarC_Reflection_V1_Data.Tv_Const
                                                                    uu___6 ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    (x0,
                                                                    FStarC_Tactics_Types.Continue)))
                                                                    | 
                                                                    FStarC_Reflection_V1_Data.Tv_Uvar
                                                                    (uu___6,
                                                                    uu___7)
                                                                    ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    (x0,
                                                                    FStarC_Tactics_Types.Continue)))
                                                                    | 
                                                                    FStarC_Reflection_V1_Data.Tv_Let
                                                                    (recf,
                                                                    attrs,
                                                                    bv, ty,
                                                                    def,
                                                                    body) ->
                                                                    Obj.repr
                                                                    (let uu___6
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Pervasives_Native.Some
                                                                    (TC_Typ
                                                                    (ty, [],
                                                                    Prims.int_zero)))) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (509))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (509))
                                                                    (Prims.of_int (39)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (509))
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (516))
                                                                    (Prims.of_int (30)))))
                                                                    (Obj.magic
                                                                    uu___6)
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    def_c ->
                                                                    let uu___7
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    fun x1 ->
                                                                    explore_term
                                                                    dbg dfs
                                                                    () f x1
                                                                    ge0 pl1
                                                                    def_c def)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (510))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (510))
                                                                    (Prims.of_int (68)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (510))
                                                                    (Prims.of_int (71))
                                                                    (Prims.of_int (516))
                                                                    (Prims.of_int (30)))))
                                                                    (Obj.magic
                                                                    uu___7)
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    explore_def
                                                                    ->
                                                                    let uu___8
                                                                    =
                                                                    FStar_InteractiveHelpers_Base.genv_push_bv
                                                                    ge0 bv ty
                                                                    false
                                                                    (FStar_Pervasives_Native.Some
                                                                    def) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (512))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (512))
                                                                    (Prims.of_int (55)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (512))
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (516))
                                                                    (Prims.of_int (30)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun ge1
                                                                    ->
                                                                    let uu___9
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    fun x1 ->
                                                                    explore_term
                                                                    dbg dfs
                                                                    () f x1
                                                                    ge1 pl1
                                                                    c0 body)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (513))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (513))
                                                                    (Prims.of_int (67)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (513))
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (516))
                                                                    (Prims.of_int (30)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    explore_next
                                                                    ->
                                                                    let uu___10
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    if dfs
                                                                    then
                                                                    (explore_next,
                                                                    explore_def)
                                                                    else
                                                                    (explore_def,
                                                                    explore_next))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (515))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (515))
                                                                    (Prims.of_int (93)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (513))
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (516))
                                                                    (Prims.of_int (30)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    match uu___11
                                                                    with
                                                                    | 
                                                                    (expl1,
                                                                    expl2) ->
                                                                    Obj.magic
                                                                    (bind_expl
                                                                    x0 expl1
                                                                    expl2))
                                                                    uu___11)))
                                                                    uu___10)))
                                                                    uu___9)))
                                                                    uu___8)))
                                                                    uu___7))
                                                                    | 
                                                                    FStarC_Reflection_V1_Data.Tv_Match
                                                                    (scrutinee,
                                                                    _ret_opt,
                                                                    branches)
                                                                    ->
                                                                    Obj.repr
                                                                    (let uu___6
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    fun
                                                                    x_flag ->
                                                                    fun br ->
                                                                    let uu___8
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    x_flag)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (520))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (520))
                                                                    (Prims.of_int (29)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (519))
                                                                    (Prims.of_int (86))
                                                                    (Prims.of_int (530))
                                                                    (Prims.of_int (21)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    match uu___9
                                                                    with
                                                                    | 
                                                                    (x01,
                                                                    flag1) ->
                                                                    if
                                                                    flag1 =
                                                                    FStarC_Tactics_Types.Continue
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___10
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    -> br)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (522))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (522))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (521))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (528))
                                                                    (Prims.of_int (42)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    match uu___11
                                                                    with
                                                                    | 
                                                                    (pat,
                                                                    branch_body)
                                                                    ->
                                                                    let uu___12
                                                                    =
                                                                    explore_pattern
                                                                    dbg dfs
                                                                    () f x01
                                                                    ge0 pat in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (524))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (524))
                                                                    (Prims.of_int (70)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (522))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (528))
                                                                    (Prims.of_int (42)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    match uu___13
                                                                    with
                                                                    | 
                                                                    (ge1, x1,
                                                                    flag11)
                                                                    ->
                                                                    if
                                                                    flag11 =
                                                                    FStarC_Tactics_Types.Continue
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (explore_term
                                                                    dbg dfs
                                                                    () f x1
                                                                    ge1 pl1
                                                                    c0
                                                                    branch_body))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    (x1,
                                                                    (convert_ctrl_flag
                                                                    flag11))))))
                                                                    uu___13)))
                                                                    uu___11)))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (x01,
                                                                    flag1)))))
                                                                    uu___9))) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (519))
                                                                    (Prims.of_int (86))
                                                                    (Prims.of_int (530))
                                                                    (Prims.of_int (21)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (531))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (536))
                                                                    (Prims.of_int (42)))))
                                                                    (Obj.magic
                                                                    uu___6)
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    explore_branch
                                                                    ->
                                                                    let uu___7
                                                                    =
                                                                    safe_typ_or_comp
                                                                    dbg
                                                                    ge0.FStar_InteractiveHelpers_Base.env
                                                                    scrutinee in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (533))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (533))
                                                                    (Prims.of_int (58)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (533))
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (536))
                                                                    (Prims.of_int (42)))))
                                                                    (Obj.magic
                                                                    uu___7)
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    scrut_c
                                                                    ->
                                                                    let uu___8
                                                                    =
                                                                    explore_term
                                                                    dbg dfs
                                                                    () f x0
                                                                    ge0 pl1
                                                                    scrut_c
                                                                    scrutinee in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (534))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (534))
                                                                    (Prims.of_int (69)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (536))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (536))
                                                                    (Prims.of_int (42)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun x1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Util.fold_left
                                                                    explore_branch
                                                                    x1
                                                                    branches))
                                                                    uu___9)))
                                                                    uu___8)))
                                                                    uu___7))
                                                                    | 
                                                                    FStarC_Reflection_V1_Data.Tv_AscribedT
                                                                    (e, ty,
                                                                    tac,
                                                                    uu___6)
                                                                    ->
                                                                    Obj.repr
                                                                    (let uu___7
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Pervasives_Native.Some
                                                                    (TC_Typ
                                                                    (ty, [],
                                                                    Prims.int_zero)))) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (538))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (538))
                                                                    (Prims.of_int (36)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (538))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (542))
                                                                    (Prims.of_int (37)))))
                                                                    (Obj.magic
                                                                    uu___7)
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun c1
                                                                    ->
                                                                    let uu___8
                                                                    =
                                                                    explore_term
                                                                    dbg dfs
                                                                    () f x0
                                                                    ge0 pl1
                                                                    FStar_Pervasives_Native.None
                                                                    ty in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (539))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (539))
                                                                    (Prims.of_int (65)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (538))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (542))
                                                                    (Prims.of_int (37)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    match uu___9
                                                                    with
                                                                    | 
                                                                    (x1,
                                                                    flag1) ->
                                                                    if
                                                                    flag1 =
                                                                    FStarC_Tactics_Types.Continue
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (explore_term
                                                                    dbg dfs
                                                                    () f x1
                                                                    ge0 pl1
                                                                    c1 e))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (x1,
                                                                    (convert_ctrl_flag
                                                                    flag1))))))
                                                                    uu___9)))
                                                                    uu___8))
                                                                    | 
                                                                    FStarC_Reflection_V1_Data.Tv_AscribedC
                                                                    (e, c1,
                                                                    tac,
                                                                    uu___6)
                                                                    ->
                                                                    Obj.repr
                                                                    (explore_term
                                                                    dbg dfs
                                                                    () f x0
                                                                    ge0 pl1
                                                                    (FStar_Pervasives_Native.Some
                                                                    (TC_Comp
                                                                    (c1, [],
                                                                    Prims.int_zero)))
                                                                    e)
                                                                    | 
                                                                    uu___6 ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    (x0,
                                                                    FStarC_Tactics_Types.Continue)))))
                                                                 else
                                                                   Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    (x0,
                                                                    (convert_ctrl_flag
                                                                    flag))))))
                                                                uu___6)))
                                                 uu___4))) uu___3))) uu___1)
and (explore_pattern :
  Prims.bool ->
    Prims.bool ->
      unit ->
        Obj.t explorer ->
          Obj.t ->
            FStar_InteractiveHelpers_Base.genv ->
              FStarC_Reflection_V1_Data.pattern ->
                ((FStar_InteractiveHelpers_Base.genv * Obj.t *
                   FStarC_Tactics_Types.ctrl_flag),
                  unit) FStar_Tactics_Effect.tac_repr)
  =
  fun dbg ->
    fun dfs ->
      fun a ->
        fun f ->
          fun x ->
            fun ge0 ->
              fun pat ->
                let uu___ =
                  FStar_InteractiveHelpers_Base.print_dbg dbg
                    "[> explore_pattern:" in
                FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range
                           "FStar.InteractiveHelpers.ExploreTerm.fst"
                           (Prims.of_int (553)) (Prims.of_int (2))
                           (Prims.of_int (553)) (Prims.of_int (39)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range
                           "FStar.InteractiveHelpers.ExploreTerm.fst"
                           (Prims.of_int (554)) (Prims.of_int (2))
                           (Prims.of_int (570)) (Prims.of_int (38)))))
                  (Obj.magic uu___)
                  (fun uu___1 ->
                     (fun uu___1 ->
                        match pat with
                        | FStarC_Reflection_V1_Data.Pat_Constant uu___2 ->
                            Obj.magic
                              (Obj.repr
                                 (FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___3 ->
                                       (ge0, x,
                                         FStarC_Tactics_Types.Continue))))
                        | FStarC_Reflection_V1_Data.Pat_Cons
                            (fv, us, patterns) ->
                            Obj.magic
                              (Obj.repr
                                 (let uu___2 =
                                    Obj.magic
                                      (FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___3 ->
                                            fun ge_x_flag ->
                                              fun pat1 ->
                                                let uu___4 =
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___5 ->
                                                          ge_x_flag)) in
                                                FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                           (Prims.of_int (558))
                                                           (Prims.of_int (25))
                                                           (Prims.of_int (558))
                                                           (Prims.of_int (34)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                           (Prims.of_int (557))
                                                           (Prims.of_int (35))
                                                           (Prims.of_int (564))
                                                           (Prims.of_int (20)))))
                                                  (Obj.magic uu___4)
                                                  (fun uu___5 ->
                                                     (fun uu___5 ->
                                                        match uu___5 with
                                                        | (ge01, x1, flag) ->
                                                            let uu___6 =
                                                              Obj.magic
                                                                (FStar_Tactics_Effect.lift_div_tac
                                                                   (fun
                                                                    uu___7 ->
                                                                    pat1)) in
                                                            Obj.magic
                                                              (FStar_Tactics_Effect.tac_bind
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (559))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (559))
                                                                    (Prims.of_int (23)))))
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (558))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (564))
                                                                    (Prims.of_int (20)))))
                                                                 (Obj.magic
                                                                    uu___6)
                                                                 (fun uu___7
                                                                    ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    match uu___7
                                                                    with
                                                                    | 
                                                                    (pat11,
                                                                    uu___8)
                                                                    ->
                                                                    if
                                                                    flag =
                                                                    FStarC_Tactics_Types.Continue
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (explore_pattern
                                                                    dbg dfs
                                                                    () f x1
                                                                    ge01
                                                                    pat11))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (ge01,
                                                                    x1, flag)))))
                                                                    uu___7)))
                                                       uu___5))) in
                                  FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.InteractiveHelpers.ExploreTerm.fst"
                                             (Prims.of_int (557))
                                             (Prims.of_int (35))
                                             (Prims.of_int (564))
                                             (Prims.of_int (20)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.InteractiveHelpers.ExploreTerm.fst"
                                             (Prims.of_int (566))
                                             (Prims.of_int (4))
                                             (Prims.of_int (566))
                                             (Prims.of_int (53)))))
                                    (Obj.magic uu___2)
                                    (fun uu___3 ->
                                       (fun explore_pat ->
                                          Obj.magic
                                            (FStar_Tactics_Util.fold_left
                                               explore_pat
                                               (ge0, x,
                                                 FStarC_Tactics_Types.Continue)
                                               patterns)) uu___3)))
                        | FStarC_Reflection_V1_Data.Pat_Var (bv, st) ->
                            Obj.magic
                              (Obj.repr
                                 (let uu___2 =
                                    let uu___3 =
                                      FStarC_Tactics_Unseal.unseal st in
                                    FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "FStar.InteractiveHelpers.ExploreTerm.fst"
                                               (Prims.of_int (568))
                                               (Prims.of_int (34))
                                               (Prims.of_int (568))
                                               (Prims.of_int (45)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "FStar.InteractiveHelpers.ExploreTerm.fst"
                                               (Prims.of_int (568))
                                               (Prims.of_int (14))
                                               (Prims.of_int (568))
                                               (Prims.of_int (56)))))
                                      (Obj.magic uu___3)
                                      (fun uu___4 ->
                                         (fun uu___4 ->
                                            Obj.magic
                                              (FStar_InteractiveHelpers_Base.genv_push_bv
                                                 ge0 bv uu___4 false
                                                 FStar_Pervasives_Native.None))
                                           uu___4) in
                                  FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.InteractiveHelpers.ExploreTerm.fst"
                                             (Prims.of_int (568))
                                             (Prims.of_int (14))
                                             (Prims.of_int (568))
                                             (Prims.of_int (56)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.InteractiveHelpers.ExploreTerm.fst"
                                             (Prims.of_int (569))
                                             (Prims.of_int (4))
                                             (Prims.of_int (569))
                                             (Prims.of_int (20)))))
                                    (Obj.magic uu___2)
                                    (fun ge1 ->
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___3 ->
                                            (ge1, x,
                                              FStarC_Tactics_Types.Continue)))))
                        | FStarC_Reflection_V1_Data.Pat_Dot_Term uu___2 ->
                            Obj.magic
                              (Obj.repr
                                 (FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___3 ->
                                       (ge0, x,
                                         FStarC_Tactics_Types.Continue)))))
                       uu___1)
let (free_in :
  FStarC_Reflection_Types.term ->
    (FStarC_Reflection_Types.bv Prims.list, unit)
      FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    let uu___ =
      Obj.magic
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___1 ->
              fun bv1 ->
                fun bv2 ->
                  let uu___2 = FStar_Tactics_V1_Derived.name_of_bv bv1 in
                  FStar_Tactics_Effect.tac_bind
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range
                             "FStar.InteractiveHelpers.ExploreTerm.fst"
                             (Prims.of_int (577)) (Prims.of_int (4))
                             (Prims.of_int (577)) (Prims.of_int (18)))))
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range
                             "FStar.InteractiveHelpers.ExploreTerm.fst"
                             (Prims.of_int (577)) (Prims.of_int (4))
                             (Prims.of_int (577)) (Prims.of_int (35)))))
                    (Obj.magic uu___2)
                    (fun uu___3 ->
                       (fun uu___3 ->
                          let uu___4 =
                            FStar_Tactics_V1_Derived.name_of_bv bv2 in
                          Obj.magic
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "FStar.InteractiveHelpers.ExploreTerm.fst"
                                        (Prims.of_int (577))
                                        (Prims.of_int (21))
                                        (Prims.of_int (577))
                                        (Prims.of_int (35)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "FStar.InteractiveHelpers.ExploreTerm.fst"
                                        (Prims.of_int (577))
                                        (Prims.of_int (4))
                                        (Prims.of_int (577))
                                        (Prims.of_int (35)))))
                               (Obj.magic uu___4)
                               (fun uu___5 ->
                                  FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___6 -> uu___3 = uu___5)))) uu___3))) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.InteractiveHelpers.ExploreTerm.fst"
               (Prims.of_int (577)) (Prims.of_int (4)) (Prims.of_int (577))
               (Prims.of_int (35)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.InteractiveHelpers.ExploreTerm.fst"
               (Prims.of_int (578)) (Prims.of_int (4)) (Prims.of_int (596))
               (Prims.of_int (75))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun same_name ->
            let uu___1 =
              Obj.magic
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___7 ->
                      fun uu___6 ->
                        fun uu___5 ->
                          fun uu___4 ->
                            fun uu___3 ->
                              fun uu___2 ->
                                (fun uu___2 ->
                                   fun fl ->
                                     fun ge ->
                                       fun pl ->
                                         fun c ->
                                           fun tv ->
                                             match tv with
                                             | FStarC_Reflection_V1_Data.Tv_Var
                                                 bv ->
                                                 Obj.magic
                                                   (Obj.repr
                                                      (let uu___3 =
                                                         let uu___4 =
                                                           FStar_Tactics_V1_Derived.name_of_bv
                                                             bv in
                                                         FStar_Tactics_Effect.tac_bind
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (585))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (585))
                                                                    (Prims.of_int (55)))))
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (585))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (585))
                                                                    (Prims.of_int (55)))))
                                                           (Obj.magic uu___4)
                                                           (fun uu___5 ->
                                                              (fun uu___5 ->
                                                                 Obj.magic
                                                                   (FStar_InteractiveHelpers_Base.genv_get_from_name
                                                                    ge uu___5))
                                                                uu___5) in
                                                       FStar_Tactics_Effect.tac_bind
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                  (Prims.of_int (585))
                                                                  (Prims.of_int (18))
                                                                  (Prims.of_int (585))
                                                                  (Prims.of_int (55)))))
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                  (Prims.of_int (585))
                                                                  (Prims.of_int (12))
                                                                  (Prims.of_int (590))
                                                                  (Prims.of_int (30)))))
                                                         (Obj.magic uu___3)
                                                         (fun uu___4 ->
                                                            (fun uu___4 ->
                                                               match uu___4
                                                               with
                                                               | FStar_Pervasives_Native.None
                                                                   ->
                                                                   Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___5
                                                                    =
                                                                    let uu___6
                                                                    =
                                                                    FStar_Tactics_Util.tryFind
                                                                    (same_name
                                                                    bv) fl in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (588))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (588))
                                                                    (Prims.of_int (54)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (588))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (588))
                                                                    (Prims.of_int (76)))))
                                                                    (Obj.magic
                                                                    uu___6)
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    if uu___7
                                                                    then fl
                                                                    else bv
                                                                    :: fl)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (588))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (588))
                                                                    (Prims.of_int (76)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (589))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (589))
                                                                    (Prims.of_int (21)))))
                                                                    (Obj.magic
                                                                    uu___5)
                                                                    (fun fl'
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fl',
                                                                    FStarC_Tactics_Types.Continue)))))
                                                               | FStar_Pervasives_Native.Some
                                                                   uu___5 ->
                                                                   Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fl,
                                                                    FStarC_Tactics_Types.Continue)))))
                                                              uu___4)))
                                             | FStarC_Reflection_V1_Data.Tv_BVar
                                                 bv ->
                                                 Obj.magic
                                                   (Obj.repr
                                                      (let uu___3 =
                                                         let uu___4 =
                                                           FStar_Tactics_V1_Derived.name_of_bv
                                                             bv in
                                                         FStar_Tactics_Effect.tac_bind
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (585))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (585))
                                                                    (Prims.of_int (55)))))
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (585))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (585))
                                                                    (Prims.of_int (55)))))
                                                           (Obj.magic uu___4)
                                                           (fun uu___5 ->
                                                              (fun uu___5 ->
                                                                 Obj.magic
                                                                   (FStar_InteractiveHelpers_Base.genv_get_from_name
                                                                    ge uu___5))
                                                                uu___5) in
                                                       FStar_Tactics_Effect.tac_bind
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                  (Prims.of_int (585))
                                                                  (Prims.of_int (18))
                                                                  (Prims.of_int (585))
                                                                  (Prims.of_int (55)))))
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                  (Prims.of_int (585))
                                                                  (Prims.of_int (12))
                                                                  (Prims.of_int (590))
                                                                  (Prims.of_int (30)))))
                                                         (Obj.magic uu___3)
                                                         (fun uu___4 ->
                                                            (fun uu___4 ->
                                                               match uu___4
                                                               with
                                                               | FStar_Pervasives_Native.None
                                                                   ->
                                                                   Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___5
                                                                    =
                                                                    let uu___6
                                                                    =
                                                                    FStar_Tactics_Util.tryFind
                                                                    (same_name
                                                                    bv) fl in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (588))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (588))
                                                                    (Prims.of_int (54)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (588))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (588))
                                                                    (Prims.of_int (76)))))
                                                                    (Obj.magic
                                                                    uu___6)
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    if uu___7
                                                                    then fl
                                                                    else bv
                                                                    :: fl)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (588))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (588))
                                                                    (Prims.of_int (76)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (589))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (589))
                                                                    (Prims.of_int (21)))))
                                                                    (Obj.magic
                                                                    uu___5)
                                                                    (fun fl'
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fl',
                                                                    FStarC_Tactics_Types.Continue)))))
                                                               | FStar_Pervasives_Native.Some
                                                                   uu___5 ->
                                                                   Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fl,
                                                                    FStarC_Tactics_Types.Continue)))))
                                                              uu___4)))
                                             | uu___3 ->
                                                 Obj.magic
                                                   (Obj.repr
                                                      (FStar_Tactics_Effect.lift_div_tac
                                                         (fun uu___4 ->
                                                            (fl,
                                                              FStarC_Tactics_Types.Continue)))))
                                  uu___7 uu___6 uu___5 uu___4 uu___3 uu___2)) in
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range
                          "FStar.InteractiveHelpers.ExploreTerm.fst"
                          (Prims.of_int (582)) (Prims.of_int (4))
                          (Prims.of_int (592)) (Prims.of_int (23)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range
                          "FStar.InteractiveHelpers.ExploreTerm.fst"
                          (Prims.of_int (593)) (Prims.of_int (4))
                          (Prims.of_int (596)) (Prims.of_int (75)))))
                 (Obj.magic uu___1)
                 (fun uu___2 ->
                    (fun update_free ->
                       let uu___2 = FStarC_Tactics_V1_Builtins.top_env () in
                       Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.InteractiveHelpers.ExploreTerm.fst"
                                     (Prims.of_int (594)) (Prims.of_int (10))
                                     (Prims.of_int (594)) (Prims.of_int (20)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.InteractiveHelpers.ExploreTerm.fst"
                                     (Prims.of_int (594)) (Prims.of_int (23))
                                     (Prims.of_int (596)) (Prims.of_int (75)))))
                            (Obj.magic uu___2)
                            (fun uu___3 ->
                               (fun e ->
                                  let uu___3 =
                                    Obj.magic
                                      (FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___4 ->
                                            FStar_InteractiveHelpers_Base.mk_genv
                                              e [] [])) in
                                  Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                (Prims.of_int (595))
                                                (Prims.of_int (11))
                                                (Prims.of_int (595))
                                                (Prims.of_int (26)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                (Prims.of_int (596))
                                                (Prims.of_int (2))
                                                (Prims.of_int (596))
                                                (Prims.of_int (75)))))
                                       (Obj.magic uu___3)
                                       (fun uu___4 ->
                                          (fun ge ->
                                             let uu___4 =
                                               let uu___5 =
                                                 Obj.magic
                                                   (explore_term false false
                                                      ()
                                                      (Obj.magic update_free)
                                                      (Obj.magic []) ge []
                                                      FStar_Pervasives_Native.None
                                                      t) in
                                               FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                          (Prims.of_int (596))
                                                          (Prims.of_int (20))
                                                          (Prims.of_int (596))
                                                          (Prims.of_int (74)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                          (Prims.of_int (596))
                                                          (Prims.of_int (15))
                                                          (Prims.of_int (596))
                                                          (Prims.of_int (75)))))
                                                 (Obj.magic uu___5)
                                                 (fun uu___6 ->
                                                    FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___7 ->
                                                         FStar_Pervasives_Native.fst
                                                           uu___6)) in
                                             Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                           (Prims.of_int (596))
                                                           (Prims.of_int (15))
                                                           (Prims.of_int (596))
                                                           (Prims.of_int (75)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                           (Prims.of_int (596))
                                                           (Prims.of_int (2))
                                                           (Prims.of_int (596))
                                                           (Prims.of_int (75)))))
                                                  (Obj.magic uu___4)
                                                  (fun uu___5 ->
                                                     FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___6 ->
                                                          FStar_List_Tot_Base.rev
                                                            uu___5)))) uu___4)))
                                 uu___3))) uu___2))) uu___1)
let (abs_free_in :
  FStar_InteractiveHelpers_Base.genv ->
    FStarC_Reflection_Types.term ->
      ((FStarC_Reflection_Types.bv * FStarC_Reflection_Types.typ) Prims.list,
        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun ge ->
    fun t ->
      let uu___ = free_in t in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range
                 "FStar.InteractiveHelpers.ExploreTerm.fst"
                 (Prims.of_int (602)) (Prims.of_int (12))
                 (Prims.of_int (602)) (Prims.of_int (21)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range
                 "FStar.InteractiveHelpers.ExploreTerm.fst"
                 (Prims.of_int (602)) (Prims.of_int (24))
                 (Prims.of_int (610)) (Prims.of_int (9))))) (Obj.magic uu___)
        (fun fvl ->
           FStar_Tactics_Effect.lift_div_tac
             (fun uu___1 ->
                FStar_List_Tot_Base.concatMap
                  (fun uu___2 ->
                     match uu___2 with
                     | (bv, ty) ->
                         if
                           FStar_Pervasives_Native.uu___is_Some
                             (FStar_List_Tot_Base.find
                                (FStar_InteractiveHelpers_Base.bv_eq bv) fvl)
                         then [(bv, ty)]
                         else [])
                  (FStar_List_Tot_Base.rev
                     (FStar_InteractiveHelpers_Base.genv_abstract_bvs ge))))
let (shadowed_free_in :
  FStar_InteractiveHelpers_Base.genv ->
    FStarC_Reflection_Types.term ->
      (FStarC_Reflection_Types.bv Prims.list, unit)
        FStar_Tactics_Effect.tac_repr)
  =
  fun ge ->
    fun t ->
      let uu___ = free_in t in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range
                 "FStar.InteractiveHelpers.ExploreTerm.fst"
                 (Prims.of_int (615)) (Prims.of_int (12))
                 (Prims.of_int (615)) (Prims.of_int (21)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range
                 "FStar.InteractiveHelpers.ExploreTerm.fst"
                 (Prims.of_int (616)) (Prims.of_int (2)) (Prims.of_int (616))
                 (Prims.of_int (54))))) (Obj.magic uu___)
        (fun fvl ->
           FStar_Tactics_Effect.lift_div_tac
             (fun uu___1 ->
                FStar_List_Tot_Base.filter
                  (fun bv ->
                     FStar_InteractiveHelpers_Base.bv_is_shadowed ge bv) fvl))
let (term_has_shadowed_variables :
  FStar_InteractiveHelpers_Base.genv ->
    FStarC_Reflection_Types.term ->
      (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun ge ->
    fun t ->
      let uu___ = free_in t in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range
                 "FStar.InteractiveHelpers.ExploreTerm.fst"
                 (Prims.of_int (621)) (Prims.of_int (12))
                 (Prims.of_int (621)) (Prims.of_int (21)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range
                 "FStar.InteractiveHelpers.ExploreTerm.fst"
                 (Prims.of_int (622)) (Prims.of_int (2)) (Prims.of_int (622))
                 (Prims.of_int (50))))) (Obj.magic uu___)
        (fun fvl ->
           FStar_Tactics_Effect.lift_div_tac
             (fun uu___1 ->
                FStar_Pervasives_Native.uu___is_Some
                  (FStar_List_Tot_Base.tryFind
                     (FStar_InteractiveHelpers_Base.bv_is_shadowed ge) fvl)))