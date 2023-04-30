open Prims
let (pure_effect_qn : Prims.string) = "Prims.PURE"
let (pure_hoare_effect_qn : Prims.string) = "Prims.Pure"
let (stack_effect_qn : Prims.string) = "FStar.HyperStack.ST.Stack"
let (st_effect_qn : Prims.string) = "FStar.HyperStack.ST.ST"
let (comp_qualifier :
  FStar_Reflection_Types.comp ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    (fun c ->
       Obj.magic
         (FStar_Tactics_Effect.lift_div_tac
            (fun uu___ ->
               match FStar_Reflection_Builtins.inspect_comp c with
               | FStar_Reflection_Data.C_Total uu___1 -> "C_Total"
               | FStar_Reflection_Data.C_GTotal uu___1 -> "C_GTotal"
               | FStar_Reflection_Data.C_Lemma (uu___1, uu___2, uu___3) ->
                   "C_Lemma"
               | FStar_Reflection_Data.C_Eff
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
let (effect_name_to_type : FStar_Reflection_Types.name -> effect_type) =
  fun ename ->
    let ename1 = FStar_Reflection_Derived.flatten_name ename in
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
  ty: FStar_Reflection_Types.typ ;
  refin: FStar_Reflection_Types.term FStar_Pervasives_Native.option }
let (__proj__Mktype_info__item__ty : type_info -> FStar_Reflection_Types.typ)
  = fun projectee -> match projectee with | { ty; refin;_} -> ty
let (__proj__Mktype_info__item__refin :
  type_info -> FStar_Reflection_Types.term FStar_Pervasives_Native.option) =
  fun projectee -> match projectee with | { ty; refin;_} -> refin
let (mk_type_info :
  FStar_Reflection_Types.typ ->
    FStar_Reflection_Types.term FStar_Pervasives_Native.option -> type_info)
  = fun uu___ -> fun uu___1 -> { ty = uu___; refin = uu___1 }
let (type_info_to_string :
  type_info -> (Prims.string, unit) FStar_Tactics_Effect.tac_repr) =
  fun info ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Range.mk_range "FStar.InteractiveHelpers.ExploreTerm.fst"
         (Prims.of_int (84)) (Prims.of_int (2)) (Prims.of_int (85))
         (Prims.of_int (50)))
      (FStar_Range.mk_range "prims.fst" (Prims.of_int (590))
         (Prims.of_int (19)) (Prims.of_int (590)) (Prims.of_int (31)))
      (Obj.magic
         (FStar_Tactics_Effect.tac_bind
            (FStar_Range.mk_range "FStar.InteractiveHelpers.ExploreTerm.fst"
               (Prims.of_int (84)) (Prims.of_int (2)) (Prims.of_int (84))
               (Prims.of_int (24)))
            (FStar_Range.mk_range "FStar.InteractiveHelpers.ExploreTerm.fst"
               (Prims.of_int (84)) (Prims.of_int (2)) (Prims.of_int (85))
               (Prims.of_int (50)))
            (Obj.magic (FStar_Tactics_Builtins.term_to_string info.ty))
            (fun uu___ ->
               (fun uu___ ->
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Range.mk_range
                          "FStar.InteractiveHelpers.ExploreTerm.fst"
                          (Prims.of_int (84)) (Prims.of_int (27))
                          (Prims.of_int (85)) (Prims.of_int (50)))
                       (FStar_Range.mk_range "prims.fst" (Prims.of_int (590))
                          (Prims.of_int (19)) (Prims.of_int (590))
                          (Prims.of_int (31)))
                       (Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Range.mk_range
                                "FStar.InteractiveHelpers.ExploreTerm.fst"
                                (Prims.of_int (85)) (Prims.of_int (2))
                                (Prims.of_int (85)) (Prims.of_int (50)))
                             (FStar_Range.mk_range "prims.fst"
                                (Prims.of_int (590)) (Prims.of_int (19))
                                (Prims.of_int (590)) (Prims.of_int (31)))
                             (Obj.magic
                                (FStar_Tactics_Effect.tac_bind
                                   (FStar_Range.mk_range
                                      "FStar.InteractiveHelpers.ExploreTerm.fst"
                                      (Prims.of_int (85)) (Prims.of_int (2))
                                      (Prims.of_int (85)) (Prims.of_int (44)))
                                   (FStar_Range.mk_range "prims.fst"
                                      (Prims.of_int (590))
                                      (Prims.of_int (19))
                                      (Prims.of_int (590))
                                      (Prims.of_int (31)))
                                   (Obj.magic
                                      (FStar_InteractiveHelpers_Base.option_to_string
                                         FStar_Tactics_Builtins.term_to_string
                                         info.refin))
                                   (fun uu___1 ->
                                      FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___2 ->
                                           Prims.strcat uu___1 ")"))))
                             (fun uu___1 ->
                                FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___2 -> Prims.strcat ") (" uu___1))))
                       (fun uu___1 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___2 -> Prims.strcat uu___ uu___1))))
                 uu___)))
      (fun uu___ ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___1 -> Prims.strcat "Mktype_info (" uu___))
let (unit_type_info : type_info) =
  mk_type_info
    (FStar_Reflection_Builtins.pack_ln
       (FStar_Reflection_Data.Tv_FVar
          (FStar_Reflection_Builtins.pack_fv ["Prims"; "unit"])))
    FStar_Pervasives_Native.None
let (safe_tc :
  FStar_Reflection_Types.env ->
    FStar_Reflection_Types.term ->
      (FStar_Reflection_Types.term FStar_Pervasives_Native.option, unit)
        FStar_Tactics_Effect.tac_repr)
  =
  fun e ->
    fun t ->
      FStar_Tactics_Derived.try_with
        (fun uu___ ->
           match () with
           | () ->
               FStar_Tactics_Effect.tac_bind
                 (FStar_Range.mk_range
                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                    (Prims.of_int (91)) (Prims.of_int (11))
                    (Prims.of_int (91)) (Prims.of_int (19)))
                 (FStar_Range.mk_range
                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                    (Prims.of_int (91)) (Prims.of_int (6))
                    (Prims.of_int (91)) (Prims.of_int (19)))
                 (Obj.magic (FStar_Tactics_Builtins.tc e t))
                 (fun uu___1 ->
                    FStar_Tactics_Effect.lift_div_tac
                      (fun uu___2 -> FStar_Pervasives_Native.Some uu___1)))
        (fun uu___ ->
           (fun uu___ ->
              Obj.magic
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___1 -> FStar_Pervasives_Native.None))) uu___)
let (safe_tcc :
  FStar_Reflection_Types.env ->
    FStar_Reflection_Types.term ->
      (FStar_Reflection_Types.comp FStar_Pervasives_Native.option, unit)
        FStar_Tactics_Effect.tac_repr)
  =
  fun e ->
    fun t ->
      FStar_Tactics_Derived.try_with
        (fun uu___ ->
           match () with
           | () ->
               FStar_Tactics_Effect.tac_bind
                 (FStar_Range.mk_range
                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                    (Prims.of_int (95)) (Prims.of_int (11))
                    (Prims.of_int (95)) (Prims.of_int (20)))
                 (FStar_Range.mk_range
                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                    (Prims.of_int (95)) (Prims.of_int (6))
                    (Prims.of_int (95)) (Prims.of_int (20)))
                 (Obj.magic (FStar_Tactics_Builtins.tcc e t))
                 (fun uu___1 ->
                    FStar_Tactics_Effect.lift_div_tac
                      (fun uu___2 -> FStar_Pervasives_Native.Some uu___1)))
        (fun uu___ ->
           (fun uu___ ->
              Obj.magic
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___1 -> FStar_Pervasives_Native.None))) uu___)
let (get_type_info_from_type :
  FStar_Reflection_Types.typ ->
    (type_info, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun ty ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Range.mk_range "FStar.InteractiveHelpers.ExploreTerm.fst"
         (Prims.of_int (98)) (Prims.of_int (8)) (Prims.of_int (98))
         (Prims.of_int (18)))
      (FStar_Range.mk_range "FStar.InteractiveHelpers.ExploreTerm.fst"
         (Prims.of_int (98)) (Prims.of_int (2)) (Prims.of_int (107))
         (Prims.of_int (24))) (Obj.magic (FStar_Tactics_Builtins.inspect ty))
      (fun uu___ ->
         (fun uu___ ->
            match uu___ with
            | FStar_Reflection_Data.Tv_Refine (bv, sort, refin) ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Range.mk_range
                        "FStar.InteractiveHelpers.ExploreTerm.fst"
                        (Prims.of_int (100)) (Prims.of_int (19))
                        (Prims.of_int (100)) (Prims.of_int (43)))
                     (FStar_Range.mk_range
                        "FStar.InteractiveHelpers.ExploreTerm.fst"
                        (Prims.of_int (101)) (Prims.of_int (4))
                        (Prims.of_int (104)) (Prims.of_int (38)))
                     (Obj.magic
                        (FStar_InteractiveHelpers_Base.prettify_term false
                           sort))
                     (fun uu___1 ->
                        (fun raw_type ->
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Range.mk_range
                                   "FStar.InteractiveHelpers.ExploreTerm.fst"
                                   (Prims.of_int (101)) (Prims.of_int (21))
                                   (Prims.of_int (101)) (Prims.of_int (38)))
                                (FStar_Range.mk_range
                                   "FStar.InteractiveHelpers.ExploreTerm.fst"
                                   (Prims.of_int (102)) (Prims.of_int (4))
                                   (Prims.of_int (104)) (Prims.of_int (38)))
                                (FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___1 ->
                                      FStar_Reflection_Derived.mk_binder bv
                                        sort))
                                (fun uu___1 ->
                                   (fun b ->
                                      Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Range.mk_range
                                              "FStar.InteractiveHelpers.ExploreTerm.fst"
                                              (Prims.of_int (102))
                                              (Prims.of_int (16))
                                              (Prims.of_int (102))
                                              (Prims.of_int (41)))
                                           (FStar_Range.mk_range
                                              "FStar.InteractiveHelpers.ExploreTerm.fst"
                                              (Prims.of_int (103))
                                              (Prims.of_int (4))
                                              (Prims.of_int (104))
                                              (Prims.of_int (38)))
                                           (Obj.magic
                                              (FStar_InteractiveHelpers_Base.prettify_term
                                                 false refin))
                                           (fun uu___1 ->
                                              (fun refin1 ->
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Range.mk_range
                                                         "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                         (Prims.of_int (103))
                                                         (Prims.of_int (16))
                                                         (Prims.of_int (103))
                                                         (Prims.of_int (37)))
                                                      (FStar_Range.mk_range
                                                         "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                         (Prims.of_int (104))
                                                         (Prims.of_int (4))
                                                         (Prims.of_int (104))
                                                         (Prims.of_int (38)))
                                                      (Obj.magic
                                                         (FStar_Tactics_Builtins.pack
                                                            (FStar_Reflection_Data.Tv_Abs
                                                               (b, refin1))))
                                                      (fun refin2 ->
                                                         FStar_Tactics_Effect.lift_div_tac
                                                           (fun uu___1 ->
                                                              mk_type_info
                                                                raw_type
                                                                (FStar_Pervasives_Native.Some
                                                                   refin2)))))
                                                uu___1))) uu___1))) uu___1))
            | uu___1 ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Range.mk_range
                        "FStar.InteractiveHelpers.ExploreTerm.fst"
                        (Prims.of_int (106)) (Prims.of_int (13))
                        (Prims.of_int (106)) (Prims.of_int (35)))
                     (FStar_Range.mk_range
                        "FStar.InteractiveHelpers.ExploreTerm.fst"
                        (Prims.of_int (107)) (Prims.of_int (4))
                        (Prims.of_int (107)) (Prims.of_int (24)))
                     (Obj.magic
                        (FStar_InteractiveHelpers_Base.prettify_term false ty))
                     (fun ty1 ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___2 ->
                             mk_type_info ty1 FStar_Pervasives_Native.None))))
           uu___)
let (get_type_info :
  FStar_Reflection_Types.env ->
    FStar_Reflection_Types.term ->
      (type_info FStar_Pervasives_Native.option, unit)
        FStar_Tactics_Effect.tac_repr)
  =
  fun e ->
    fun t ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Range.mk_range "FStar.InteractiveHelpers.ExploreTerm.fst"
           (Prims.of_int (111)) (Prims.of_int (8)) (Prims.of_int (111))
           (Prims.of_int (19)))
        (FStar_Range.mk_range "FStar.InteractiveHelpers.ExploreTerm.fst"
           (Prims.of_int (111)) (Prims.of_int (2)) (Prims.of_int (113))
           (Prims.of_int (48))) (Obj.magic (safe_tc e t))
        (fun uu___ ->
           (fun uu___ ->
              match uu___ with
              | FStar_Pervasives_Native.None ->
                  Obj.magic
                    (Obj.repr
                       (FStar_Tactics_Effect.lift_div_tac
                          (fun uu___1 -> FStar_Pervasives_Native.None)))
              | FStar_Pervasives_Native.Some ty ->
                  Obj.magic
                    (Obj.repr
                       (FStar_Tactics_Effect.tac_bind
                          (FStar_Range.mk_range
                             "FStar.InteractiveHelpers.ExploreTerm.fst"
                             (Prims.of_int (113)) (Prims.of_int (20))
                             (Prims.of_int (113)) (Prims.of_int (48)))
                          (FStar_Range.mk_range
                             "FStar.InteractiveHelpers.ExploreTerm.fst"
                             (Prims.of_int (113)) (Prims.of_int (15))
                             (Prims.of_int (113)) (Prims.of_int (48)))
                          (Obj.magic (get_type_info_from_type ty))
                          (fun uu___1 ->
                             FStar_Tactics_Effect.lift_div_tac
                               (fun uu___2 ->
                                  FStar_Pervasives_Native.Some uu___1)))))
             uu___)
let (get_total_or_gtotal_ret_type :
  FStar_Reflection_Types.comp ->
    FStar_Reflection_Types.typ FStar_Pervasives_Native.option)
  =
  fun c ->
    match FStar_Reflection_Builtins.inspect_comp c with
    | FStar_Reflection_Data.C_Total ret_ty ->
        FStar_Pervasives_Native.Some ret_ty
    | FStar_Reflection_Data.C_GTotal ret_ty ->
        FStar_Pervasives_Native.Some ret_ty
    | uu___ -> FStar_Pervasives_Native.None
let (get_comp_ret_type :
  FStar_Reflection_Types.comp -> FStar_Reflection_Types.typ) =
  fun c ->
    match FStar_Reflection_Builtins.inspect_comp c with
    | FStar_Reflection_Data.C_Total ret_ty -> ret_ty
    | FStar_Reflection_Data.C_GTotal ret_ty -> ret_ty
    | FStar_Reflection_Data.C_Eff (uu___, uu___1, ret_ty, uu___2, uu___3) ->
        ret_ty
    | FStar_Reflection_Data.C_Lemma (uu___, uu___1, uu___2) ->
        FStar_Reflection_Builtins.pack_ln
          (FStar_Reflection_Data.Tv_FVar
             (FStar_Reflection_Builtins.pack_fv ["Prims"; "unit"]))
let (is_total_or_gtotal : FStar_Reflection_Types.comp -> Prims.bool) =
  fun c ->
    FStar_Pervasives_Native.uu___is_Some (get_total_or_gtotal_ret_type c)
let (is_unit_type :
  FStar_Reflection_Types.typ ->
    (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun ty ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Range.mk_range "FStar.InteractiveHelpers.ExploreTerm.fst"
         (Prims.of_int (135)) (Prims.of_int (8)) (Prims.of_int (135))
         (Prims.of_int (18)))
      (FStar_Range.mk_range "FStar.InteractiveHelpers.ExploreTerm.fst"
         (Prims.of_int (135)) (Prims.of_int (2)) (Prims.of_int (137))
         (Prims.of_int (14))) (Obj.magic (FStar_Tactics_Builtins.inspect ty))
      (fun uu___ ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___1 ->
              match uu___ with
              | FStar_Reflection_Data.Tv_FVar fv ->
                  FStar_InteractiveHelpers_Base.fv_eq_name fv
                    FStar_Reflection_Const.unit_lid
              | uu___2 -> false))
type typ_or_comp =
  | TC_Typ of FStar_Reflection_Types.typ * FStar_Reflection_Types.binder
  Prims.list * Prims.nat 
  | TC_Comp of FStar_Reflection_Types.comp * FStar_Reflection_Types.binder
  Prims.list * Prims.nat 
let (uu___is_TC_Typ : typ_or_comp -> Prims.bool) =
  fun projectee ->
    match projectee with
    | TC_Typ (v, pl, num_unflushed) -> true
    | uu___ -> false
let (__proj__TC_Typ__item__v : typ_or_comp -> FStar_Reflection_Types.typ) =
  fun projectee -> match projectee with | TC_Typ (v, pl, num_unflushed) -> v
let (__proj__TC_Typ__item__pl :
  typ_or_comp -> FStar_Reflection_Types.binder Prims.list) =
  fun projectee -> match projectee with | TC_Typ (v, pl, num_unflushed) -> pl
let (__proj__TC_Typ__item__num_unflushed : typ_or_comp -> Prims.nat) =
  fun projectee ->
    match projectee with | TC_Typ (v, pl, num_unflushed) -> num_unflushed
let (uu___is_TC_Comp : typ_or_comp -> Prims.bool) =
  fun projectee ->
    match projectee with
    | TC_Comp (v, pl, num_unflushed) -> true
    | uu___ -> false
let (__proj__TC_Comp__item__v : typ_or_comp -> FStar_Reflection_Types.comp) =
  fun projectee -> match projectee with | TC_Comp (v, pl, num_unflushed) -> v
let (__proj__TC_Comp__item__pl :
  typ_or_comp -> FStar_Reflection_Types.binder Prims.list) =
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
        FStar_Tactics_Effect.tac_bind
          (FStar_Range.mk_range "FStar.InteractiveHelpers.ExploreTerm.fst"
             (Prims.of_int (163)) (Prims.of_int (17)) (Prims.of_int (164))
             (Prims.of_int (37)))
          (FStar_Range.mk_range "prims.fst" (Prims.of_int (590))
             (Prims.of_int (19)) (Prims.of_int (590)) (Prims.of_int (31)))
          (Obj.magic
             (FStar_Tactics_Effect.tac_bind
                (FStar_Range.mk_range
                   "FStar.InteractiveHelpers.ExploreTerm.fst"
                   (Prims.of_int (163)) (Prims.of_int (17))
                   (Prims.of_int (163)) (Prims.of_int (33)))
                (FStar_Range.mk_range
                   "FStar.InteractiveHelpers.ExploreTerm.fst"
                   (Prims.of_int (163)) (Prims.of_int (17))
                   (Prims.of_int (164)) (Prims.of_int (37)))
                (Obj.magic (FStar_Tactics_Builtins.term_to_string v))
                (fun uu___ ->
                   (fun uu___ ->
                      Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Range.mk_range
                              "FStar.InteractiveHelpers.ExploreTerm.fst"
                              (Prims.of_int (163)) (Prims.of_int (36))
                              (Prims.of_int (164)) (Prims.of_int (37)))
                           (FStar_Range.mk_range "prims.fst"
                              (Prims.of_int (590)) (Prims.of_int (19))
                              (Prims.of_int (590)) (Prims.of_int (31)))
                           (Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Range.mk_range
                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                    (Prims.of_int (163)) (Prims.of_int (43))
                                    (Prims.of_int (164)) (Prims.of_int (37)))
                                 (FStar_Range.mk_range "prims.fst"
                                    (Prims.of_int (590)) (Prims.of_int (19))
                                    (Prims.of_int (590)) (Prims.of_int (31)))
                                 (Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Range.mk_range
                                          "FStar.InteractiveHelpers.ExploreTerm.fst"
                                          (Prims.of_int (163))
                                          (Prims.of_int (43))
                                          (Prims.of_int (163))
                                          (Prims.of_int (88)))
                                       (FStar_Range.mk_range "prims.fst"
                                          (Prims.of_int (590))
                                          (Prims.of_int (19))
                                          (Prims.of_int (590))
                                          (Prims.of_int (31)))
                                       (Obj.magic
                                          (FStar_InteractiveHelpers_Base.list_to_string
                                             (fun b ->
                                                FStar_Tactics_Derived.name_of_binder
                                                  b) pl))
                                       (fun uu___1 ->
                                          FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___2 ->
                                               Prims.strcat uu___1
                                                 (Prims.strcat " "
                                                    (Prims.string_of_int
                                                       num_unflushed))))))
                                 (fun uu___1 ->
                                    FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___2 -> Prims.strcat ") " uu___1))))
                           (fun uu___1 ->
                              FStar_Tactics_Effect.lift_div_tac
                                (fun uu___2 -> Prims.strcat uu___ uu___1))))
                     uu___)))
          (fun uu___ ->
             FStar_Tactics_Effect.lift_div_tac
               (fun uu___1 -> Prims.strcat "TC_Typ (" uu___))
    | TC_Comp (c, pl, num_unflushed) ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Range.mk_range "FStar.InteractiveHelpers.ExploreTerm.fst"
             (Prims.of_int (166)) (Prims.of_int (18)) (Prims.of_int (167))
             (Prims.of_int (37)))
          (FStar_Range.mk_range "prims.fst" (Prims.of_int (590))
             (Prims.of_int (19)) (Prims.of_int (590)) (Prims.of_int (31)))
          (Obj.magic
             (FStar_Tactics_Effect.tac_bind
                (FStar_Range.mk_range
                   "FStar.InteractiveHelpers.ExploreTerm.fst"
                   (Prims.of_int (166)) (Prims.of_int (18))
                   (Prims.of_int (166)) (Prims.of_int (35)))
                (FStar_Range.mk_range
                   "FStar.InteractiveHelpers.ExploreTerm.fst"
                   (Prims.of_int (166)) (Prims.of_int (18))
                   (Prims.of_int (167)) (Prims.of_int (37)))
                (Obj.magic (FStar_InteractiveHelpers_Base.acomp_to_string c))
                (fun uu___ ->
                   (fun uu___ ->
                      Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Range.mk_range
                              "FStar.InteractiveHelpers.ExploreTerm.fst"
                              (Prims.of_int (166)) (Prims.of_int (38))
                              (Prims.of_int (167)) (Prims.of_int (37)))
                           (FStar_Range.mk_range "prims.fst"
                              (Prims.of_int (590)) (Prims.of_int (19))
                              (Prims.of_int (590)) (Prims.of_int (31)))
                           (Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Range.mk_range
                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                    (Prims.of_int (166)) (Prims.of_int (45))
                                    (Prims.of_int (167)) (Prims.of_int (37)))
                                 (FStar_Range.mk_range "prims.fst"
                                    (Prims.of_int (590)) (Prims.of_int (19))
                                    (Prims.of_int (590)) (Prims.of_int (31)))
                                 (Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Range.mk_range
                                          "FStar.InteractiveHelpers.ExploreTerm.fst"
                                          (Prims.of_int (166))
                                          (Prims.of_int (45))
                                          (Prims.of_int (166))
                                          (Prims.of_int (90)))
                                       (FStar_Range.mk_range "prims.fst"
                                          (Prims.of_int (590))
                                          (Prims.of_int (19))
                                          (Prims.of_int (590))
                                          (Prims.of_int (31)))
                                       (Obj.magic
                                          (FStar_InteractiveHelpers_Base.list_to_string
                                             (fun b ->
                                                FStar_Tactics_Derived.name_of_binder
                                                  b) pl))
                                       (fun uu___1 ->
                                          FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___2 ->
                                               Prims.strcat uu___1
                                                 (Prims.strcat " "
                                                    (Prims.string_of_int
                                                       num_unflushed))))))
                                 (fun uu___1 ->
                                    FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___2 -> Prims.strcat ") " uu___1))))
                           (fun uu___1 ->
                              FStar_Tactics_Effect.lift_div_tac
                                (fun uu___2 -> Prims.strcat uu___ uu___1))))
                     uu___)))
          (fun uu___ ->
             FStar_Tactics_Effect.lift_div_tac
               (fun uu___1 -> Prims.strcat "TC_Comp (" uu___))
let (params_of_typ_or_comp :
  typ_or_comp -> FStar_Reflection_Types.binder Prims.list) =
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
    FStar_Reflection_Types.env ->
      FStar_Reflection_Types.term ->
        (typ_or_comp FStar_Pervasives_Native.option, unit)
          FStar_Tactics_Effect.tac_repr)
  =
  fun dbg ->
    fun e ->
      fun t ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Range.mk_range "FStar.InteractiveHelpers.ExploreTerm.fst"
             (Prims.of_int (183)) (Prims.of_int (8)) (Prims.of_int (183))
             (Prims.of_int (20)))
          (FStar_Range.mk_range "FStar.InteractiveHelpers.ExploreTerm.fst"
             (Prims.of_int (183)) (Prims.of_int (2)) (Prims.of_int (193))
             (Prims.of_int (25))) (Obj.magic (safe_tcc e t))
          (fun uu___ ->
             (fun uu___ ->
                match uu___ with
                | FStar_Pervasives_Native.None ->
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Range.mk_range
                            "FStar.InteractiveHelpers.ExploreTerm.fst"
                            (Prims.of_int (185)) (Prims.of_int (4))
                            (Prims.of_int (187)) (Prims.of_int (35)))
                         (FStar_Range.mk_range
                            "FStar.InteractiveHelpers.ExploreTerm.fst"
                            (Prims.of_int (188)) (Prims.of_int (4))
                            (Prims.of_int (188)) (Prims.of_int (8)))
                         (Obj.magic
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Range.mk_range
                                  "FStar.InteractiveHelpers.ExploreTerm.fst"
                                  (Prims.of_int (185)) (Prims.of_int (18))
                                  (Prims.of_int (187)) (Prims.of_int (35)))
                               (FStar_Range.mk_range
                                  "FStar.InteractiveHelpers.ExploreTerm.fst"
                                  (Prims.of_int (185)) (Prims.of_int (4))
                                  (Prims.of_int (187)) (Prims.of_int (35)))
                               (Obj.magic
                                  (FStar_Tactics_Effect.tac_bind
                                     (FStar_Range.mk_range
                                        "FStar.InteractiveHelpers.ExploreTerm.fst"
                                        (Prims.of_int (186))
                                        (Prims.of_int (19))
                                        (Prims.of_int (187))
                                        (Prims.of_int (34)))
                                     (FStar_Range.mk_range "prims.fst"
                                        (Prims.of_int (590))
                                        (Prims.of_int (19))
                                        (Prims.of_int (590))
                                        (Prims.of_int (31)))
                                     (Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Range.mk_range
                                              "FStar.InteractiveHelpers.ExploreTerm.fst"
                                              (Prims.of_int (186))
                                              (Prims.of_int (33))
                                              (Prims.of_int (187))
                                              (Prims.of_int (34)))
                                           (FStar_Range.mk_range "prims.fst"
                                              (Prims.of_int (590))
                                              (Prims.of_int (19))
                                              (Prims.of_int (590))
                                              (Prims.of_int (31)))
                                           (Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Range.mk_range
                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                    (Prims.of_int (186))
                                                    (Prims.of_int (33))
                                                    (Prims.of_int (186))
                                                    (Prims.of_int (49)))
                                                 (FStar_Range.mk_range
                                                    "prims.fst"
                                                    (Prims.of_int (590))
                                                    (Prims.of_int (19))
                                                    (Prims.of_int (590))
                                                    (Prims.of_int (31)))
                                                 (Obj.magic
                                                    (FStar_Tactics_Builtins.term_to_string
                                                       t))
                                                 (fun uu___1 ->
                                                    FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___2 ->
                                                         Prims.strcat uu___1
                                                           "\n-comp: None"))))
                                           (fun uu___1 ->
                                              FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___2 ->
                                                   Prims.strcat "\n-term: "
                                                     uu___1))))
                                     (fun uu___1 ->
                                        FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___2 ->
                                             Prims.strcat
                                               "[> safe_typ_or_comp:" uu___1))))
                               (fun uu___1 ->
                                  (fun uu___1 ->
                                     Obj.magic
                                       (FStar_InteractiveHelpers_Base.print_dbg
                                          dbg uu___1)) uu___1)))
                         (fun uu___1 ->
                            FStar_Tactics_Effect.lift_div_tac
                              (fun uu___2 -> FStar_Pervasives_Native.None)))
                | FStar_Pervasives_Native.Some c ->
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Range.mk_range
                            "FStar.InteractiveHelpers.ExploreTerm.fst"
                            (Prims.of_int (190)) (Prims.of_int (4))
                            (Prims.of_int (192)) (Prims.of_int (51)))
                         (FStar_Range.mk_range
                            "FStar.InteractiveHelpers.ExploreTerm.fst"
                            (Prims.of_int (193)) (Prims.of_int (4))
                            (Prims.of_int (193)) (Prims.of_int (25)))
                         (Obj.magic
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Range.mk_range
                                  "FStar.InteractiveHelpers.ExploreTerm.fst"
                                  (Prims.of_int (190)) (Prims.of_int (18))
                                  (Prims.of_int (192)) (Prims.of_int (51)))
                               (FStar_Range.mk_range
                                  "FStar.InteractiveHelpers.ExploreTerm.fst"
                                  (Prims.of_int (190)) (Prims.of_int (4))
                                  (Prims.of_int (192)) (Prims.of_int (51)))
                               (Obj.magic
                                  (FStar_Tactics_Effect.tac_bind
                                     (FStar_Range.mk_range
                                        "FStar.InteractiveHelpers.ExploreTerm.fst"
                                        (Prims.of_int (191))
                                        (Prims.of_int (19))
                                        (Prims.of_int (192))
                                        (Prims.of_int (50)))
                                     (FStar_Range.mk_range "prims.fst"
                                        (Prims.of_int (590))
                                        (Prims.of_int (19))
                                        (Prims.of_int (590))
                                        (Prims.of_int (31)))
                                     (Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Range.mk_range
                                              "FStar.InteractiveHelpers.ExploreTerm.fst"
                                              (Prims.of_int (191))
                                              (Prims.of_int (33))
                                              (Prims.of_int (192))
                                              (Prims.of_int (50)))
                                           (FStar_Range.mk_range "prims.fst"
                                              (Prims.of_int (590))
                                              (Prims.of_int (19))
                                              (Prims.of_int (590))
                                              (Prims.of_int (31)))
                                           (Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Range.mk_range
                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                    (Prims.of_int (191))
                                                    (Prims.of_int (33))
                                                    (Prims.of_int (191))
                                                    (Prims.of_int (49)))
                                                 (FStar_Range.mk_range
                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                    (Prims.of_int (191))
                                                    (Prims.of_int (33))
                                                    (Prims.of_int (192))
                                                    (Prims.of_int (50)))
                                                 (Obj.magic
                                                    (FStar_Tactics_Builtins.term_to_string
                                                       t))
                                                 (fun uu___1 ->
                                                    (fun uu___1 ->
                                                       Obj.magic
                                                         (FStar_Tactics_Effect.tac_bind
                                                            (FStar_Range.mk_range
                                                               "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                               (Prims.of_int (192))
                                                               (Prims.of_int (19))
                                                               (Prims.of_int (192))
                                                               (Prims.of_int (50)))
                                                            (FStar_Range.mk_range
                                                               "prims.fst"
                                                               (Prims.of_int (590))
                                                               (Prims.of_int (19))
                                                               (Prims.of_int (590))
                                                               (Prims.of_int (31)))
                                                            (Obj.magic
                                                               (FStar_Tactics_Effect.tac_bind
                                                                  (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (192))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (192))
                                                                    (Prims.of_int (50)))
                                                                  (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))
                                                                  (Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.acomp_to_string
                                                                    c))
                                                                  (fun uu___2
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Prims.strcat
                                                                    "\n-comp: "
                                                                    uu___2))))
                                                            (fun uu___2 ->
                                                               FStar_Tactics_Effect.lift_div_tac
                                                                 (fun uu___3
                                                                    ->
                                                                    Prims.strcat
                                                                    uu___1
                                                                    uu___2))))
                                                      uu___1)))
                                           (fun uu___1 ->
                                              FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___2 ->
                                                   Prims.strcat "\n-term: "
                                                     uu___1))))
                                     (fun uu___1 ->
                                        FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___2 ->
                                             Prims.strcat
                                               "[> safe_typ_or_comp:" uu___1))))
                               (fun uu___1 ->
                                  (fun uu___1 ->
                                     Obj.magic
                                       (FStar_InteractiveHelpers_Base.print_dbg
                                          dbg uu___1)) uu___1)))
                         (fun uu___1 ->
                            FStar_Tactics_Effect.lift_div_tac
                              (fun uu___2 ->
                                 FStar_Pervasives_Native.Some
                                   (TC_Comp (c, [], Prims.int_zero))))))
               uu___)
let (subst_bv_in_comp :
  FStar_Reflection_Types.env ->
    FStar_Reflection_Types.bv ->
      FStar_Reflection_Types.typ ->
        FStar_Reflection_Types.term ->
          FStar_Reflection_Types.comp ->
            (FStar_Reflection_Types.comp, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun e ->
    fun b ->
      fun sort ->
        fun t ->
          fun c ->
            FStar_InteractiveHelpers_Base.apply_subst_in_comp e c
              [((b, sort), t)]
let (subst_binder_in_comp :
  FStar_Reflection_Types.env ->
    FStar_Reflection_Types.binder ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.comp ->
          (FStar_Reflection_Types.comp, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun e ->
    fun b ->
      fun t ->
        fun c ->
          FStar_Tactics_Effect.tac_bind
            (FStar_Range.mk_range "FStar.InteractiveHelpers.ExploreTerm.fst"
               (Prims.of_int (201)) (Prims.of_int (38)) (Prims.of_int (201))
               (Prims.of_int (53)))
            (FStar_Range.mk_range "FStar.InteractiveHelpers.ExploreTerm.fst"
               (Prims.of_int (201)) (Prims.of_int (2)) (Prims.of_int (201))
               (Prims.of_int (57)))
            (Obj.magic (FStar_Tactics_Derived.binder_sort b))
            (fun uu___ ->
               (fun uu___ ->
                  Obj.magic
                    (subst_bv_in_comp e
                       (FStar_Reflection_Derived.bv_of_binder b) uu___ t c))
                 uu___)
let rec (unfold_until_arrow :
  FStar_Reflection_Types.env ->
    FStar_Reflection_Types.typ ->
      (FStar_Reflection_Types.typ, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun e ->
    fun ty0 ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Range.mk_range "FStar.InteractiveHelpers.ExploreTerm.fst"
           (Prims.of_int (207)) (Prims.of_int (5)) (Prims.of_int (207))
           (Prims.of_int (28)))
        (FStar_Range.mk_range "FStar.InteractiveHelpers.ExploreTerm.fst"
           (Prims.of_int (207)) (Prims.of_int (2)) (Prims.of_int (251))
           (Prims.of_int (7)))
        (Obj.magic
           (FStar_Tactics_Effect.tac_bind
              (FStar_Range.mk_range
                 "FStar.InteractiveHelpers.ExploreTerm.fst"
                 (Prims.of_int (207)) (Prims.of_int (15))
                 (Prims.of_int (207)) (Prims.of_int (28)))
              (FStar_Range.mk_range
                 "FStar.InteractiveHelpers.ExploreTerm.fst"
                 (Prims.of_int (207)) (Prims.of_int (5)) (Prims.of_int (207))
                 (Prims.of_int (28)))
              (Obj.magic (FStar_Tactics_Builtins.inspect ty0))
              (fun uu___ ->
                 FStar_Tactics_Effect.lift_div_tac
                   (fun uu___1 ->
                      FStar_Reflection_Data.uu___is_Tv_Arrow uu___))))
        (fun uu___ ->
           (fun uu___ ->
              if uu___
              then
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> ty0)))
              else
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.tac_bind
                        (FStar_Range.mk_range
                           "FStar.InteractiveHelpers.ExploreTerm.fst"
                           (Prims.of_int (211)) (Prims.of_int (13))
                           (Prims.of_int (211)) (Prims.of_int (35)))
                        (FStar_Range.mk_range
                           "FStar.InteractiveHelpers.ExploreTerm.fst"
                           (Prims.of_int (213)) (Prims.of_int (4))
                           (Prims.of_int (250)) (Prims.of_int (75)))
                        (Obj.magic
                           (FStar_Tactics_Builtins.norm_term_env e [] ty0))
                        (fun uu___2 ->
                           (fun ty ->
                              Obj.magic
                                (FStar_Tactics_Effect.tac_bind
                                   (FStar_Range.mk_range
                                      "FStar.InteractiveHelpers.ExploreTerm.fst"
                                      (Prims.of_int (214)) (Prims.of_int (6))
                                      (Prims.of_int (224)) (Prims.of_int (9)))
                                   (FStar_Range.mk_range
                                      "FStar.InteractiveHelpers.ExploreTerm.fst"
                                      (Prims.of_int (227)) (Prims.of_int (4))
                                      (Prims.of_int (250))
                                      (Prims.of_int (75)))
                                   (FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___2 ->
                                         fun fv ->
                                           FStar_Tactics_Effect.tac_bind
                                             (FStar_Range.mk_range
                                                "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                (Prims.of_int (214))
                                                (Prims.of_int (15))
                                                (Prims.of_int (214))
                                                (Prims.of_int (32)))
                                             (FStar_Range.mk_range
                                                "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                (Prims.of_int (215))
                                                (Prims.of_int (6))
                                                (Prims.of_int (224))
                                                (Prims.of_int (9)))
                                             (Obj.magic
                                                (FStar_Tactics_Builtins.pack
                                                   (FStar_Reflection_Data.Tv_FVar
                                                      fv)))
                                             (fun uu___3 ->
                                                (fun ty1 ->
                                                   Obj.magic
                                                     (FStar_Tactics_Effect.tac_bind
                                                        (FStar_Range.mk_range
                                                           "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                           (Prims.of_int (215))
                                                           (Prims.of_int (16))
                                                           (Prims.of_int (215))
                                                           (Prims.of_int (44)))
                                                        (FStar_Range.mk_range
                                                           "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                           (Prims.of_int (217))
                                                           (Prims.of_int (6))
                                                           (Prims.of_int (224))
                                                           (Prims.of_int (9)))
                                                        (FStar_Tactics_Effect.lift_div_tac
                                                           (fun uu___3 ->
                                                              FStar_Reflection_Derived.flatten_name
                                                                (FStar_Reflection_Builtins.inspect_fv
                                                                   fv)))
                                                        (fun uu___3 ->
                                                           (fun fvn ->
                                                              Obj.magic
                                                                (FStar_Tactics_Effect.tac_bind
                                                                   (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (217))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (217))
                                                                    (Prims.of_int (53)))
                                                                   (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (219))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (223))
                                                                    (Prims.of_int (16)))
                                                                   (Obj.magic
                                                                    (FStar_Tactics_Builtins.norm_term_env
                                                                    e
                                                                    [
                                                                    FStar_Pervasives.delta_only
                                                                    [fvn]]
                                                                    ty1))
                                                                   (fun
                                                                    uu___3 ->
                                                                    (fun ty'
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (219))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (219))
                                                                    (Prims.of_int (29)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (219))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (223))
                                                                    (Prims.of_int (16)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Builtins.inspect
                                                                    ty'))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    FStar_Reflection_Data.Tv_FVar
                                                                    fv' ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (if
                                                                    (FStar_Reflection_Derived.flatten_name
                                                                    (FStar_Reflection_Builtins.inspect_fv
                                                                    fv')) =
                                                                    fvn
                                                                    then
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (222))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (222))
                                                                    (Prims.of_int (82)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (222))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (222))
                                                                    (Prims.of_int (82)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (222))
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (222))
                                                                    (Prims.of_int (81)))
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Builtins.term_to_string
                                                                    ty0))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Prims.strcat
                                                                    "unfold_until_arrow: could not unfold: "
                                                                    uu___4))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.mfail
                                                                    uu___4))
                                                                    uu___4))
                                                                    else
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    ty'))))
                                                                    | 
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    ty'))))
                                                                    uu___3)))
                                                                    uu___3)))
                                                             uu___3))) uu___3)))
                                   (fun uu___2 ->
                                      (fun unfold_fv ->
                                         Obj.magic
                                           (FStar_Tactics_Effect.tac_bind
                                              (FStar_Range.mk_range
                                                 "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                 (Prims.of_int (227))
                                                 (Prims.of_int (10))
                                                 (Prims.of_int (227))
                                                 (Prims.of_int (20)))
                                              (FStar_Range.mk_range
                                                 "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                 (Prims.of_int (227))
                                                 (Prims.of_int (4))
                                                 (Prims.of_int (250))
                                                 (Prims.of_int (75)))
                                              (Obj.magic
                                                 (FStar_Tactics_Builtins.inspect
                                                    ty))
                                              (fun uu___2 ->
                                                 (fun uu___2 ->
                                                    match uu___2 with
                                                    | FStar_Reflection_Data.Tv_Arrow
                                                        (uu___3, uu___4) ->
                                                        Obj.magic
                                                          (Obj.repr
                                                             (FStar_Tactics_Effect.lift_div_tac
                                                                (fun uu___5
                                                                   -> ty)))
                                                    | FStar_Reflection_Data.Tv_FVar
                                                        fv ->
                                                        Obj.magic
                                                          (Obj.repr
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Range.mk_range
                                                                   "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                   (Prims.of_int (231))
                                                                   (Prims.of_int (16))
                                                                   (Prims.of_int (231))
                                                                   (Prims.of_int (28)))
                                                                (FStar_Range.mk_range
                                                                   "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                   (Prims.of_int (232))
                                                                   (Prims.of_int (6))
                                                                   (Prims.of_int (232))
                                                                   (Prims.of_int (30)))
                                                                (Obj.magic
                                                                   (unfold_fv
                                                                    fv))
                                                                (fun uu___3
                                                                   ->
                                                                   (fun ty'
                                                                    ->
                                                                    Obj.magic
                                                                    (unfold_until_arrow
                                                                    e ty'))
                                                                    uu___3)))
                                                    | FStar_Reflection_Data.Tv_App
                                                        (uu___3, uu___4) ->
                                                        Obj.magic
                                                          (Obj.repr
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Range.mk_range
                                                                   "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                   (Prims.of_int (235))
                                                                   (Prims.of_int (21))
                                                                   (Prims.of_int (235))
                                                                   (Prims.of_int (35)))
                                                                (FStar_Range.mk_range
                                                                   "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                   (Prims.of_int (235))
                                                                   (Prims.of_int (6))
                                                                   (Prims.of_int (242))
                                                                   (Prims.of_int (9)))
                                                                (Obj.magic
                                                                   (FStar_Tactics_SyntaxHelpers.collect_app
                                                                    ty))
                                                                (fun uu___5
                                                                   ->
                                                                   (fun
                                                                    uu___5 ->
                                                                    match uu___5
                                                                    with
                                                                    | 
                                                                    (hd,
                                                                    args) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (236))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (236))
                                                                    (Prims.of_int (28)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (236))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (82)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Builtins.inspect
                                                                    hd))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    match uu___6
                                                                    with
                                                                    | 
                                                                    FStar_Reflection_Data.Tv_FVar
                                                                    fv ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (238))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (238))
                                                                    (Prims.of_int (30)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (239))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (240))
                                                                    (Prims.of_int (32)))
                                                                    (Obj.magic
                                                                    (unfold_fv
                                                                    fv))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun hd'
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (239))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (239))
                                                                    (Prims.of_int (33)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (240))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (240))
                                                                    (Prims.of_int (32)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Reflection_Derived.mk_app
                                                                    hd' args))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun ty'
                                                                    ->
                                                                    Obj.magic
                                                                    (unfold_until_arrow
                                                                    e ty'))
                                                                    uu___7)))
                                                                    uu___7))
                                                                    | 
                                                                    uu___7 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (82)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (82)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (81)))
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Builtins.term_to_string
                                                                    ty0))
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    Prims.strcat
                                                                    "unfold_until_arrow: could not unfold: "
                                                                    uu___8))))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.mfail
                                                                    uu___8))
                                                                    uu___8)))
                                                                    uu___6)))
                                                                    uu___5)))
                                                    | FStar_Reflection_Data.Tv_Refine
                                                        (bv, sort, ref) ->
                                                        Obj.magic
                                                          (Obj.repr
                                                             (unfold_until_arrow
                                                                e sort))
                                                    | FStar_Reflection_Data.Tv_AscribedT
                                                        (body, uu___3,
                                                         uu___4, uu___5)
                                                        ->
                                                        Obj.magic
                                                          (Obj.repr
                                                             (unfold_until_arrow
                                                                e body))
                                                    | FStar_Reflection_Data.Tv_AscribedC
                                                        (body, uu___3,
                                                         uu___4, uu___5)
                                                        ->
                                                        Obj.magic
                                                          (Obj.repr
                                                             (unfold_until_arrow
                                                                e body))
                                                    | uu___3 ->
                                                        Obj.magic
                                                          (Obj.repr
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Range.mk_range
                                                                   "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                   (Prims.of_int (250))
                                                                   (Prims.of_int (12))
                                                                   (Prims.of_int (250))
                                                                   (Prims.of_int (75)))
                                                                (FStar_Range.mk_range
                                                                   "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                   (Prims.of_int (250))
                                                                   (Prims.of_int (6))
                                                                   (Prims.of_int (250))
                                                                   (Prims.of_int (75)))
                                                                (Obj.magic
                                                                   (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (250))
                                                                    (Prims.of_int (56))
                                                                    (Prims.of_int (250))
                                                                    (Prims.of_int (74)))
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Builtins.term_to_string
                                                                    ty0))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Prims.strcat
                                                                    "unfold_until_arrow: could not unfold: "
                                                                    uu___4))))
                                                                (fun uu___4
                                                                   ->
                                                                   (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.mfail
                                                                    uu___4))
                                                                    uu___4))))
                                                   uu___2))) uu___2))) uu___2))))
             uu___)
let (inst_comp_once :
  FStar_Reflection_Types.env ->
    FStar_Reflection_Types.comp ->
      FStar_Reflection_Types.term ->
        (FStar_Reflection_Types.comp, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun e ->
    fun c ->
      fun t ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Range.mk_range "FStar.InteractiveHelpers.ExploreTerm.fst"
             (Prims.of_int (256)) (Prims.of_int (11)) (Prims.of_int (256))
             (Prims.of_int (30)))
          (FStar_Range.mk_range "FStar.InteractiveHelpers.ExploreTerm.fst"
             (Prims.of_int (257)) (Prims.of_int (2)) (Prims.of_int (263))
             (Prims.of_int (5)))
          (FStar_Tactics_Effect.lift_div_tac
             (fun uu___ -> get_comp_ret_type c))
          (fun uu___ ->
             (fun ty ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Range.mk_range
                        "FStar.InteractiveHelpers.ExploreTerm.fst"
                        (Prims.of_int (257)) (Prims.of_int (12))
                        (Prims.of_int (257)) (Prims.of_int (35)))
                     (FStar_Range.mk_range
                        "FStar.InteractiveHelpers.ExploreTerm.fst"
                        (Prims.of_int (258)) (Prims.of_int (8))
                        (Prims.of_int (262)) (Prims.of_int (46)))
                     (Obj.magic (unfold_until_arrow e ty))
                     (fun uu___ ->
                        (fun ty' ->
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Range.mk_range
                                   "FStar.InteractiveHelpers.ExploreTerm.fst"
                                   (Prims.of_int (258)) (Prims.of_int (14))
                                   (Prims.of_int (258)) (Prims.of_int (25)))
                                (FStar_Range.mk_range
                                   "FStar.InteractiveHelpers.ExploreTerm.fst"
                                   (Prims.of_int (258)) (Prims.of_int (8))
                                   (Prims.of_int (262)) (Prims.of_int (46)))
                                (Obj.magic
                                   (FStar_Tactics_Builtins.inspect ty'))
                                (fun uu___ ->
                                   (fun uu___ ->
                                      match uu___ with
                                      | FStar_Reflection_Data.Tv_Arrow
                                          (b1, c1) ->
                                          Obj.magic
                                            (subst_binder_in_comp e b1 t c1)
                                      | uu___1 ->
                                          Obj.magic
                                            (FStar_InteractiveHelpers_Base.mfail
                                               "inst_comp_once: inconsistent state"))
                                     uu___))) uu___))) uu___)
let rec (inst_comp :
  FStar_Reflection_Types.env ->
    FStar_Reflection_Types.comp ->
      FStar_Reflection_Types.term Prims.list ->
        (FStar_Reflection_Types.comp, unit) FStar_Tactics_Effect.tac_repr)
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
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Range.mk_range
                              "FStar.InteractiveHelpers.ExploreTerm.fst"
                              (Prims.of_int (270)) (Prims.of_int (13))
                              (Prims.of_int (272)) (Prims.of_int (36)))
                           (FStar_Range.mk_range
                              "FStar.InteractiveHelpers.ExploreTerm.fst"
                              (Prims.of_int (274)) (Prims.of_int (4))
                              (Prims.of_int (274)) (Prims.of_int (22)))
                           (Obj.magic
                              (FStar_Tactics_Derived.try_with
                                 (fun uu___ ->
                                    match () with
                                    | () -> inst_comp_once e c t)
                                 (fun uu___ ->
                                    (fun uu___ ->
                                       match uu___ with
                                       | FStar_InteractiveHelpers_Base.MetaAnalysis
                                           msg ->
                                           Obj.magic
                                             (Obj.repr
                                                (FStar_InteractiveHelpers_Base.mfail
                                                   (Prims.strcat
                                                      "inst_comp: error: "
                                                      msg)))
                                       | err ->
                                           Obj.magic
                                             (Obj.repr
                                                (FStar_Tactics_Effect.raise
                                                   err))) uu___)))
                           (fun uu___ ->
                              (fun c' -> Obj.magic (inst_comp e c' tl'))
                                uu___)))) uu___2 uu___1 uu___
let (_abs_update_typ :
  FStar_Reflection_Types.binder ->
    FStar_Reflection_Types.typ ->
      FStar_Reflection_Types.binder Prims.list ->
        FStar_Reflection_Types.env ->
          (typ_or_comp, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun b ->
    fun ty ->
      fun pl ->
        fun e ->
          FStar_Tactics_Derived.try_with
            (fun uu___ ->
               match () with
               | () ->
                   FStar_Tactics_Effect.tac_bind
                     (FStar_Range.mk_range
                        "FStar.InteractiveHelpers.ExploreTerm.fst"
                        (Prims.of_int (289)) (Prims.of_int (14))
                        (Prims.of_int (289)) (Prims.of_int (37)))
                     (FStar_Range.mk_range
                        "FStar.InteractiveHelpers.ExploreTerm.fst"
                        (Prims.of_int (290)) (Prims.of_int (10))
                        (Prims.of_int (295)) (Prims.of_int (49)))
                     (Obj.magic (unfold_until_arrow e ty))
                     (fun uu___1 ->
                        (fun ty' ->
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Range.mk_range
                                   "FStar.InteractiveHelpers.ExploreTerm.fst"
                                   (Prims.of_int (290)) (Prims.of_int (16))
                                   (Prims.of_int (290)) (Prims.of_int (27)))
                                (FStar_Range.mk_range
                                   "FStar.InteractiveHelpers.ExploreTerm.fst"
                                   (Prims.of_int (290)) (Prims.of_int (10))
                                   (Prims.of_int (295)) (Prims.of_int (49)))
                                (Obj.magic
                                   (FStar_Tactics_Builtins.inspect ty'))
                                (fun uu___1 ->
                                   (fun uu___1 ->
                                      match uu___1 with
                                      | FStar_Reflection_Data.Tv_Arrow
                                          (b1, c1) ->
                                          Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Range.mk_range
                                                  "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                  (Prims.of_int (292))
                                                  (Prims.of_int (16))
                                                  (Prims.of_int (292))
                                                  (Prims.of_int (77)))
                                               (FStar_Range.mk_range
                                                  "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                  (Prims.of_int (293))
                                                  (Prims.of_int (6))
                                                  (Prims.of_int (293))
                                                  (Prims.of_int (29)))
                                               (Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Range.mk_range
                                                        "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                        (Prims.of_int (292))
                                                        (Prims.of_int (42))
                                                        (Prims.of_int (292))
                                                        (Prims.of_int (74)))
                                                     (FStar_Range.mk_range
                                                        "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                        (Prims.of_int (292))
                                                        (Prims.of_int (16))
                                                        (Prims.of_int (292))
                                                        (Prims.of_int (77)))
                                                     (Obj.magic
                                                        (FStar_Tactics_Builtins.pack
                                                           (FStar_Reflection_Data.Tv_Var
                                                              (FStar_Reflection_Derived.bv_of_binder
                                                                 b))))
                                                     (fun uu___2 ->
                                                        (fun uu___2 ->
                                                           Obj.magic
                                                             (subst_binder_in_comp
                                                                e b1 uu___2
                                                                c1)) uu___2)))
                                               (fun c1' ->
                                                  FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___2 ->
                                                       TC_Comp
                                                         (c1', (b :: pl),
                                                           Prims.int_zero))))
                                      | uu___2 ->
                                          Obj.magic
                                            (FStar_InteractiveHelpers_Base.mfail
                                               "_abs_update_typ: inconsistent state"))
                                     uu___1))) uu___1))
            (fun uu___ ->
               (fun uu___ ->
                  match uu___ with
                  | FStar_InteractiveHelpers_Base.MetaAnalysis msg ->
                      Obj.magic
                        (Obj.repr
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Range.mk_range
                                 "FStar.InteractiveHelpers.ExploreTerm.fst"
                                 (Prims.of_int (299)) (Prims.of_int (10))
                                 (Prims.of_int (299)) (Prims.of_int (93)))
                              (FStar_Range.mk_range
                                 "FStar.InteractiveHelpers.ExploreTerm.fst"
                                 (Prims.of_int (299)) (Prims.of_int (4))
                                 (Prims.of_int (299)) (Prims.of_int (93)))
                              (Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Range.mk_range
                                       "FStar.InteractiveHelpers.ExploreTerm.fst"
                                       (Prims.of_int (299))
                                       (Prims.of_int (61))
                                       (Prims.of_int (299))
                                       (Prims.of_int (92)))
                                    (FStar_Range.mk_range "prims.fst"
                                       (Prims.of_int (590))
                                       (Prims.of_int (19))
                                       (Prims.of_int (590))
                                       (Prims.of_int (31)))
                                    (Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Range.mk_range
                                             "FStar.InteractiveHelpers.ExploreTerm.fst"
                                             (Prims.of_int (299))
                                             (Prims.of_int (61))
                                             (Prims.of_int (299))
                                             (Prims.of_int (78)))
                                          (FStar_Range.mk_range "prims.fst"
                                             (Prims.of_int (590))
                                             (Prims.of_int (19))
                                             (Prims.of_int (590))
                                             (Prims.of_int (31)))
                                          (Obj.magic
                                             (FStar_Tactics_Builtins.term_to_string
                                                ty))
                                          (fun uu___1 ->
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___2 ->
                                                  Prims.strcat uu___1
                                                    (Prims.strcat ":\n" msg)))))
                                    (fun uu___1 ->
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___2 ->
                                            Prims.strcat
                                              "_abs_update_typ: could not find an arrow in: "
                                              uu___1))))
                              (fun uu___1 ->
                                 (fun uu___1 ->
                                    Obj.magic
                                      (FStar_InteractiveHelpers_Base.mfail
                                         uu___1)) uu___1)))
                  | err ->
                      Obj.magic (Obj.repr (FStar_Tactics_Effect.raise err)))
                 uu___)
let (abs_update_typ_or_comp :
  FStar_Reflection_Types.binder ->
    typ_or_comp ->
      FStar_Reflection_Types.env ->
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
  FStar_Reflection_Types.binder ->
    typ_or_comp FStar_Pervasives_Native.option ->
      FStar_Reflection_Types.env ->
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
                        (FStar_Tactics_Derived.try_with
                           (fun uu___ ->
                              match () with
                              | () ->
                                  FStar_Tactics_Effect.tac_bind
                                    (FStar_Range.mk_range
                                       "FStar.InteractiveHelpers.ExploreTerm.fst"
                                       (Prims.of_int (321))
                                       (Prims.of_int (14))
                                       (Prims.of_int (321))
                                       (Prims.of_int (42)))
                                    (FStar_Range.mk_range
                                       "FStar.InteractiveHelpers.ExploreTerm.fst"
                                       (Prims.of_int (322))
                                       (Prims.of_int (6))
                                       (Prims.of_int (322))
                                       (Prims.of_int (12)))
                                    (Obj.magic (abs_update_typ_or_comp b c e))
                                    (fun c1 ->
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___1 ->
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
    FStar_Reflection_Types.env ->
      FStar_Reflection_Types.binder Prims.list ->
        ((FStar_Reflection_Types.bv * FStar_Reflection_Types.typ) *
          FStar_Reflection_Types.term) Prims.list ->
          FStar_Reflection_Types.comp ->
            (FStar_Reflection_Types.comp, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun dbg ->
    fun e ->
      fun rem ->
        fun inst ->
          fun c ->
            FStar_Tactics_Effect.tac_bind
              (FStar_Range.mk_range
                 "FStar.InteractiveHelpers.ExploreTerm.fst"
                 (Prims.of_int (339)) (Prims.of_int (4)) (Prims.of_int (340))
                 (Prims.of_int (32)))
              (FStar_Range.mk_range
                 "FStar.InteractiveHelpers.ExploreTerm.fst"
                 (Prims.of_int (342)) (Prims.of_int (2)) (Prims.of_int (359))
                 (Prims.of_int (86)))
              (FStar_Tactics_Effect.lift_div_tac
                 (fun uu___ ->
                    fun c1 ->
                      fun inst1 ->
                        FStar_Tactics_Effect.tac_bind
                          (FStar_Range.mk_range
                             "FStar.InteractiveHelpers.ExploreTerm.fst"
                             (Prims.of_int (339)) (Prims.of_int (15))
                             (Prims.of_int (339)) (Prims.of_int (28)))
                          (FStar_Range.mk_range
                             "FStar.InteractiveHelpers.ExploreTerm.fst"
                             (Prims.of_int (340)) (Prims.of_int (4))
                             (Prims.of_int (340)) (Prims.of_int (32)))
                          (FStar_Tactics_Effect.lift_div_tac
                             (fun uu___1 -> FStar_List_Tot_Base.rev inst1))
                          (fun uu___1 ->
                             (fun inst2 ->
                                Obj.magic
                                  (FStar_InteractiveHelpers_Base.apply_subst_in_comp
                                     e c1 inst2)) uu___1)))
              (fun uu___ ->
                 (fun flush ->
                    match rem with
                    | [] -> Obj.magic (flush c inst)
                    | b::rem' ->
                        Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Range.mk_range
                                "FStar.InteractiveHelpers.ExploreTerm.fst"
                                (Prims.of_int (348)) (Prims.of_int (13))
                                (Prims.of_int (348)) (Prims.of_int (32)))
                             (FStar_Range.mk_range
                                "FStar.InteractiveHelpers.ExploreTerm.fst"
                                (Prims.of_int (349)) (Prims.of_int (4))
                                (Prims.of_int (359)) (Prims.of_int (86)))
                             (FStar_Tactics_Effect.lift_div_tac
                                (fun uu___ -> get_comp_ret_type c))
                             (fun uu___ ->
                                (fun ty ->
                                   Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Range.mk_range
                                           "FStar.InteractiveHelpers.ExploreTerm.fst"
                                           (Prims.of_int (350))
                                           (Prims.of_int (6))
                                           (Prims.of_int (351))
                                           (Prims.of_int (47)))
                                        (FStar_Range.mk_range
                                           "FStar.InteractiveHelpers.ExploreTerm.fst"
                                           (Prims.of_int (349))
                                           (Prims.of_int (4))
                                           (Prims.of_int (359))
                                           (Prims.of_int (86)))
                                        (Obj.magic
                                           (FStar_Tactics_Effect.tac_bind
                                              (FStar_Range.mk_range
                                                 "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                 (Prims.of_int (350))
                                                 (Prims.of_int (9))
                                                 (Prims.of_int (350))
                                                 (Prims.of_int (31)))
                                              (FStar_Range.mk_range
                                                 "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                 (Prims.of_int (350))
                                                 (Prims.of_int (6))
                                                 (Prims.of_int (351))
                                                 (Prims.of_int (47)))
                                              (Obj.magic
                                                 (FStar_Tactics_Effect.tac_bind
                                                    (FStar_Range.mk_range
                                                       "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                       (Prims.of_int (350))
                                                       (Prims.of_int (19))
                                                       (Prims.of_int (350))
                                                       (Prims.of_int (31)))
                                                    (FStar_Range.mk_range
                                                       "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                       (Prims.of_int (350))
                                                       (Prims.of_int (9))
                                                       (Prims.of_int (350))
                                                       (Prims.of_int (31)))
                                                    (Obj.magic
                                                       (FStar_Tactics_Builtins.inspect
                                                          ty))
                                                    (fun uu___ ->
                                                       FStar_Tactics_Effect.lift_div_tac
                                                         (fun uu___1 ->
                                                            FStar_Reflection_Data.uu___is_Tv_Arrow
                                                              uu___))))
                                              (fun uu___ ->
                                                 (fun uu___ ->
                                                    if uu___
                                                    then
                                                      Obj.magic
                                                        (Obj.repr
                                                           (FStar_Tactics_Effect.lift_div_tac
                                                              (fun uu___1 ->
                                                                 (ty, inst))))
                                                    else
                                                      Obj.magic
                                                        (Obj.repr
                                                           (FStar_Tactics_Effect.tac_bind
                                                              (FStar_Range.mk_range
                                                                 "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                 (Prims.of_int (351))
                                                                 (Prims.of_int (11))
                                                                 (Prims.of_int (351))
                                                                 (Prims.of_int (43)))
                                                              (FStar_Range.mk_range
                                                                 "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                 (Prims.of_int (351))
                                                                 (Prims.of_int (11))
                                                                 (Prims.of_int (351))
                                                                 (Prims.of_int (47)))
                                                              (Obj.magic
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (351))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (351))
                                                                    (Prims.of_int (43)))
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (351))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (351))
                                                                    (Prims.of_int (43)))
                                                                    (
                                                                    Obj.magic
                                                                    (flush c
                                                                    inst))
                                                                    (
                                                                    fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    get_comp_ret_type
                                                                    uu___2))))
                                                              (fun uu___2 ->
                                                                 FStar_Tactics_Effect.lift_div_tac
                                                                   (fun
                                                                    uu___3 ->
                                                                    (uu___2,
                                                                    []))))))
                                                   uu___)))
                                        (fun uu___ ->
                                           (fun uu___ ->
                                              match uu___ with
                                              | (ty1, inst') ->
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Range.mk_range
                                                          "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                          (Prims.of_int (353))
                                                          (Prims.of_int (10))
                                                          (Prims.of_int (353))
                                                          (Prims.of_int (20)))
                                                       (FStar_Range.mk_range
                                                          "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                          (Prims.of_int (353))
                                                          (Prims.of_int (4))
                                                          (Prims.of_int (359))
                                                          (Prims.of_int (86)))
                                                       (Obj.magic
                                                          (FStar_Tactics_Builtins.inspect
                                                             ty1))
                                                       (fun uu___1 ->
                                                          (fun uu___1 ->
                                                             match uu___1
                                                             with
                                                             | FStar_Reflection_Data.Tv_Arrow
                                                                 (b', c') ->
                                                                 Obj.magic
                                                                   (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (355))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (355))
                                                                    (Prims.of_int (116)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (355))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (355))
                                                                    (Prims.of_int (119)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (355))
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (355))
                                                                    (Prims.of_int (109)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (355))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (355))
                                                                    (Prims.of_int (116)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (355))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (355))
                                                                    (Prims.of_int (76)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (355))
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (355))
                                                                    (Prims.of_int (109)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (355))
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (355))
                                                                    (Prims.of_int (75)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (355))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (355))
                                                                    (Prims.of_int (76)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Derived.binder_sort
                                                                    b'))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    ((FStar_Reflection_Derived.bv_of_binder
                                                                    b'),
                                                                    uu___2)))))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (355))
                                                                    (Prims.of_int (78))
                                                                    (Prims.of_int (355))
                                                                    (Prims.of_int (108)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (355))
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (355))
                                                                    (Prims.of_int (109)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Builtins.pack
                                                                    (FStar_Reflection_Data.Tv_Var
                                                                    (FStar_Reflection_Derived.bv_of_binder
                                                                    b))))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    (uu___2,
                                                                    uu___3)))))
                                                                    uu___2)))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    uu___2 ::
                                                                    inst))))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (_flush_typ_or_comp_comp
                                                                    dbg e
                                                                    rem'
                                                                    uu___2 c'))
                                                                    uu___2))
                                                             | uu___2 ->
                                                                 Obj.magic
                                                                   (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (357))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (359))
                                                                    (Prims.of_int (86)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (357))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (359))
                                                                    (Prims.of_int (86)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (358))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (359))
                                                                    (Prims.of_int (85)))
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (358))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (359))
                                                                    (Prims.of_int (85)))
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (358))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (358))
                                                                    (Prims.of_int (44)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (358))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (359))
                                                                    (Prims.of_int (85)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.acomp_to_string
                                                                    c))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (359))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (359))
                                                                    (Prims.of_int (85)))
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (359))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (359))
                                                                    (Prims.of_int (85)))
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.list_to_string
                                                                    (fun b1
                                                                    ->
                                                                    FStar_Tactics_Derived.name_of_binder
                                                                    b1) rem))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Prims.strcat
                                                                    "\n-remaning binders: "
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
                                                                    "\n-comp: "
                                                                    uu___3))))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Prims.strcat
                                                                    "_flush_typ_or_comp: inconsistent state"
                                                                    uu___3))))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.mfail
                                                                    uu___3))
                                                                    uu___3)))
                                                            uu___1))) uu___)))
                                  uu___))) uu___)
let (flush_typ_or_comp :
  Prims.bool ->
    FStar_Reflection_Types.env ->
      typ_or_comp -> (typ_or_comp, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun dbg ->
    fun e ->
      fun tyc ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Range.mk_range "FStar.InteractiveHelpers.ExploreTerm.fst"
             (Prims.of_int (363)) (Prims.of_int (4)) (Prims.of_int (366))
             (Prims.of_int (18)))
          (FStar_Range.mk_range "FStar.InteractiveHelpers.ExploreTerm.fst"
             (Prims.of_int (368)) (Prims.of_int (2)) (Prims.of_int (376))
             (Prims.of_int (25)))
          (FStar_Tactics_Effect.lift_div_tac
             (fun uu___ ->
                fun pl ->
                  fun n ->
                    fun c ->
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Range.mk_range
                           "FStar.InteractiveHelpers.ExploreTerm.fst"
                           (Prims.of_int (363)) (Prims.of_int (17))
                           (Prims.of_int (363)) (Prims.of_int (38)))
                        (FStar_Range.mk_range
                           "FStar.InteractiveHelpers.ExploreTerm.fst"
                           (Prims.of_int (363)) (Prims.of_int (4))
                           (Prims.of_int (366)) (Prims.of_int (18)))
                        (FStar_Tactics_Effect.lift_div_tac
                           (fun uu___1 -> FStar_List_Tot_Base.splitAt n pl))
                        (fun uu___1 ->
                           (fun uu___1 ->
                              match uu___1 with
                              | (pl', uu___2) ->
                                  Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Range.mk_range
                                          "FStar.InteractiveHelpers.ExploreTerm.fst"
                                          (Prims.of_int (364))
                                          (Prims.of_int (14))
                                          (Prims.of_int (364))
                                          (Prims.of_int (26)))
                                       (FStar_Range.mk_range
                                          "FStar.InteractiveHelpers.ExploreTerm.fst"
                                          (Prims.of_int (365))
                                          (Prims.of_int (4))
                                          (Prims.of_int (366))
                                          (Prims.of_int (18)))
                                       (FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___3 ->
                                             FStar_List_Tot_Base.rev pl'))
                                       (fun uu___3 ->
                                          (fun pl'1 ->
                                             Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Range.mk_range
                                                     "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                     (Prims.of_int (365))
                                                     (Prims.of_int (12))
                                                     (Prims.of_int (365))
                                                     (Prims.of_int (50)))
                                                  (FStar_Range.mk_range
                                                     "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                     (Prims.of_int (366))
                                                     (Prims.of_int (4))
                                                     (Prims.of_int (366))
                                                     (Prims.of_int (18)))
                                                  (Obj.magic
                                                     (_flush_typ_or_comp_comp
                                                        dbg e pl'1 [] c))
                                                  (fun c1 ->
                                                     FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___3 ->
                                                          TC_Comp
                                                            (c1, pl,
                                                              Prims.int_zero)))))
                                            uu___3))) uu___1)))
          (fun uu___ ->
             (fun flush_comp ->
                Obj.magic
                  (FStar_Tactics_Derived.try_with
                     (fun uu___ ->
                        match () with
                        | () ->
                            (match tyc with
                             | TC_Typ (ty, pl, n) ->
                                 FStar_Tactics_Effect.tac_bind
                                   (FStar_Range.mk_range
                                      "FStar.InteractiveHelpers.ExploreTerm.fst"
                                      (Prims.of_int (370))
                                      (Prims.of_int (12))
                                      (Prims.of_int (370))
                                      (Prims.of_int (34)))
                                   (FStar_Range.mk_range
                                      "FStar.InteractiveHelpers.ExploreTerm.fst"
                                      (Prims.of_int (371)) (Prims.of_int (4))
                                      (Prims.of_int (371))
                                      (Prims.of_int (21)))
                                   (FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___1 ->
                                         FStar_Reflection_Builtins.pack_comp
                                           (FStar_Reflection_Data.C_Total ty)))
                                   (fun uu___1 ->
                                      (fun c -> Obj.magic (flush_comp pl n c))
                                        uu___1)
                             | TC_Comp (c, pl, n) -> flush_comp pl n c))
                     (fun uu___ ->
                        (fun uu___ ->
                           match uu___ with
                           | FStar_InteractiveHelpers_Base.MetaAnalysis msg
                               ->
                               Obj.magic
                                 (Obj.repr
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Range.mk_range
                                          "FStar.InteractiveHelpers.ExploreTerm.fst"
                                          (Prims.of_int (375))
                                          (Prims.of_int (15))
                                          (Prims.of_int (375))
                                          (Prims.of_int (90)))
                                       (FStar_Range.mk_range
                                          "FStar.InteractiveHelpers.ExploreTerm.fst"
                                          (Prims.of_int (375))
                                          (Prims.of_int (9))
                                          (Prims.of_int (375))
                                          (Prims.of_int (90)))
                                       (Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Range.mk_range
                                                "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                (Prims.of_int (375))
                                                (Prims.of_int (50))
                                                (Prims.of_int (375))
                                                (Prims.of_int (89)))
                                             (FStar_Range.mk_range
                                                "prims.fst"
                                                (Prims.of_int (590))
                                                (Prims.of_int (19))
                                                (Prims.of_int (590))
                                                (Prims.of_int (31)))
                                             (Obj.magic
                                                (FStar_Tactics_Effect.tac_bind
                                                   (FStar_Range.mk_range
                                                      "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                      (Prims.of_int (375))
                                                      (Prims.of_int (50))
                                                      (Prims.of_int (375))
                                                      (Prims.of_int (75)))
                                                   (FStar_Range.mk_range
                                                      "prims.fst"
                                                      (Prims.of_int (590))
                                                      (Prims.of_int (19))
                                                      (Prims.of_int (590))
                                                      (Prims.of_int (31)))
                                                   (Obj.magic
                                                      (typ_or_comp_to_string
                                                         tyc))
                                                   (fun uu___1 ->
                                                      FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___2 ->
                                                           Prims.strcat
                                                             uu___1
                                                             (Prims.strcat
                                                                ":\n" msg)))))
                                             (fun uu___1 ->
                                                FStar_Tactics_Effect.lift_div_tac
                                                  (fun uu___2 ->
                                                     Prims.strcat
                                                       "flush_typ_or_comp failed on: "
                                                       uu___1))))
                                       (fun uu___1 ->
                                          (fun uu___1 ->
                                             Obj.magic
                                               (FStar_InteractiveHelpers_Base.mfail
                                                  uu___1)) uu___1)))
                           | err ->
                               Obj.magic
                                 (Obj.repr (FStar_Tactics_Effect.raise err)))
                          uu___))) uu___)
let (safe_arg_typ_or_comp :
  Prims.bool ->
    FStar_Reflection_Types.env ->
      FStar_Reflection_Types.term ->
        (typ_or_comp FStar_Pervasives_Native.option, unit)
          FStar_Tactics_Effect.tac_repr)
  =
  fun dbg ->
    fun e ->
      fun hd ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Range.mk_range "FStar.InteractiveHelpers.ExploreTerm.fst"
             (Prims.of_int (383)) (Prims.of_int (2)) (Prims.of_int (383))
             (Prims.of_int (62)))
          (FStar_Range.mk_range "FStar.InteractiveHelpers.ExploreTerm.fst"
             (Prims.of_int (384)) (Prims.of_int (2)) (Prims.of_int (404))
             (Prims.of_int (15)))
          (Obj.magic
             (FStar_Tactics_Effect.tac_bind
                (FStar_Range.mk_range
                   "FStar.InteractiveHelpers.ExploreTerm.fst"
                   (Prims.of_int (383)) (Prims.of_int (16))
                   (Prims.of_int (383)) (Prims.of_int (62)))
                (FStar_Range.mk_range
                   "FStar.InteractiveHelpers.ExploreTerm.fst"
                   (Prims.of_int (383)) (Prims.of_int (2))
                   (Prims.of_int (383)) (Prims.of_int (62)))
                (Obj.magic
                   (FStar_Tactics_Effect.tac_bind
                      (FStar_Range.mk_range
                         "FStar.InteractiveHelpers.ExploreTerm.fst"
                         (Prims.of_int (383)) (Prims.of_int (44))
                         (Prims.of_int (383)) (Prims.of_int (61)))
                      (FStar_Range.mk_range "prims.fst" (Prims.of_int (590))
                         (Prims.of_int (19)) (Prims.of_int (590))
                         (Prims.of_int (31)))
                      (Obj.magic (FStar_Tactics_Builtins.term_to_string hd))
                      (fun uu___ ->
                         FStar_Tactics_Effect.lift_div_tac
                           (fun uu___1 ->
                              Prims.strcat "safe_arg_typ_or_comp: " uu___))))
                (fun uu___ ->
                   (fun uu___ ->
                      Obj.magic
                        (FStar_InteractiveHelpers_Base.print_dbg dbg uu___))
                     uu___)))
          (fun uu___ ->
             (fun uu___ ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Range.mk_range
                        "FStar.InteractiveHelpers.ExploreTerm.fst"
                        (Prims.of_int (384)) (Prims.of_int (8))
                        (Prims.of_int (384)) (Prims.of_int (20)))
                     (FStar_Range.mk_range
                        "FStar.InteractiveHelpers.ExploreTerm.fst"
                        (Prims.of_int (384)) (Prims.of_int (2))
                        (Prims.of_int (404)) (Prims.of_int (15)))
                     (Obj.magic (safe_tc e hd))
                     (fun uu___1 ->
                        (fun uu___1 ->
                           match uu___1 with
                           | FStar_Pervasives_Native.None ->
                               Obj.magic
                                 (Obj.repr
                                    (FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___2 ->
                                          FStar_Pervasives_Native.None)))
                           | FStar_Pervasives_Native.Some ty ->
                               Obj.magic
                                 (Obj.repr
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Range.mk_range
                                          "FStar.InteractiveHelpers.ExploreTerm.fst"
                                          (Prims.of_int (387))
                                          (Prims.of_int (4))
                                          (Prims.of_int (387))
                                          (Prims.of_int (51)))
                                       (FStar_Range.mk_range
                                          "FStar.InteractiveHelpers.ExploreTerm.fst"
                                          (Prims.of_int (388))
                                          (Prims.of_int (4))
                                          (Prims.of_int (404))
                                          (Prims.of_int (15)))
                                       (Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Range.mk_range
                                                "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                (Prims.of_int (387))
                                                (Prims.of_int (18))
                                                (Prims.of_int (387))
                                                (Prims.of_int (51)))
                                             (FStar_Range.mk_range
                                                "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                (Prims.of_int (387))
                                                (Prims.of_int (4))
                                                (Prims.of_int (387))
                                                (Prims.of_int (51)))
                                             (Obj.magic
                                                (FStar_Tactics_Effect.tac_bind
                                                   (FStar_Range.mk_range
                                                      "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                      (Prims.of_int (387))
                                                      (Prims.of_int (33))
                                                      (Prims.of_int (387))
                                                      (Prims.of_int (50)))
                                                   (FStar_Range.mk_range
                                                      "prims.fst"
                                                      (Prims.of_int (590))
                                                      (Prims.of_int (19))
                                                      (Prims.of_int (590))
                                                      (Prims.of_int (31)))
                                                   (Obj.magic
                                                      (FStar_Tactics_Builtins.term_to_string
                                                         ty))
                                                   (fun uu___2 ->
                                                      FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___3 ->
                                                           Prims.strcat
                                                             "hd type: "
                                                             uu___2))))
                                             (fun uu___2 ->
                                                (fun uu___2 ->
                                                   Obj.magic
                                                     (FStar_InteractiveHelpers_Base.print_dbg
                                                        dbg uu___2)) uu___2)))
                                       (fun uu___2 ->
                                          (fun uu___2 ->
                                             Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Range.mk_range
                                                     "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                     (Prims.of_int (389))
                                                     (Prims.of_int (6))
                                                     (Prims.of_int (400))
                                                     (Prims.of_int (11)))
                                                  (FStar_Range.mk_range
                                                     "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                     (Prims.of_int (402))
                                                     (Prims.of_int (4))
                                                     (Prims.of_int (404))
                                                     (Prims.of_int (15)))
                                                  (Obj.magic
                                                     (FStar_Tactics_Effect.tac_bind
                                                        (FStar_Range.mk_range
                                                           "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                           (Prims.of_int (389))
                                                           (Prims.of_int (9))
                                                           (Prims.of_int (389))
                                                           (Prims.of_int (31)))
                                                        (FStar_Range.mk_range
                                                           "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                           (Prims.of_int (389))
                                                           (Prims.of_int (6))
                                                           (Prims.of_int (400))
                                                           (Prims.of_int (11)))
                                                        (Obj.magic
                                                           (FStar_Tactics_Effect.tac_bind
                                                              (FStar_Range.mk_range
                                                                 "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                 (Prims.of_int (389))
                                                                 (Prims.of_int (19))
                                                                 (Prims.of_int (389))
                                                                 (Prims.of_int (31)))
                                                              (FStar_Range.mk_range
                                                                 "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                 (Prims.of_int (389))
                                                                 (Prims.of_int (9))
                                                                 (Prims.of_int (389))
                                                                 (Prims.of_int (31)))
                                                              (Obj.magic
                                                                 (FStar_Tactics_Builtins.inspect
                                                                    ty))
                                                              (fun uu___3 ->
                                                                 FStar_Tactics_Effect.lift_div_tac
                                                                   (fun
                                                                    uu___4 ->
                                                                    FStar_Reflection_Data.uu___is_Tv_Arrow
                                                                    uu___3))))
                                                        (fun uu___3 ->
                                                           (fun uu___3 ->
                                                              if uu___3
                                                              then
                                                                Obj.magic
                                                                  (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (391))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (391))
                                                                    (Prims.of_int (50)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (386))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (386))
                                                                    (Prims.of_int (11)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    "no need to unfold the type"))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    ty)))
                                                              else
                                                                Obj.magic
                                                                  (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (396))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (396))
                                                                    (Prims.of_int (47)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (397))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (399))
                                                                    (Prims.of_int (10)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    "need to unfold the type"))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (397))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (397))
                                                                    (Prims.of_int (40)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (398))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (399))
                                                                    (Prims.of_int (10)))
                                                                    (Obj.magic
                                                                    (unfold_until_arrow
                                                                    e ty))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun ty1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (398))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (398))
                                                                    (Prims.of_int (67)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (397))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (397))
                                                                    (Prims.of_int (14)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (398))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (398))
                                                                    (Prims.of_int (67)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (398))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (398))
                                                                    (Prims.of_int (67)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (398))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (398))
                                                                    (Prims.of_int (66)))
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Builtins.term_to_string
                                                                    ty1))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    Prims.strcat
                                                                    "result of unfolding : "
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
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    ty1))))
                                                                    uu___6)))
                                                                    uu___5)))
                                                             uu___3)))
                                                  (fun uu___3 ->
                                                     (fun ty1 ->
                                                        Obj.magic
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (FStar_Range.mk_range
                                                                "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                (Prims.of_int (402))
                                                                (Prims.of_int (10))
                                                                (Prims.of_int (402))
                                                                (Prims.of_int (20)))
                                                             (FStar_Range.mk_range
                                                                "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                (Prims.of_int (402))
                                                                (Prims.of_int (4))
                                                                (Prims.of_int (404))
                                                                (Prims.of_int (15)))
                                                             (Obj.magic
                                                                (FStar_Tactics_Builtins.inspect
                                                                   ty1))
                                                             (fun uu___3 ->
                                                                FStar_Tactics_Effect.lift_div_tac
                                                                  (fun uu___4
                                                                    ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    FStar_Reflection_Data.Tv_Arrow
                                                                    (b, c) ->
                                                                    FStar_Pervasives_Native.Some
                                                                    (TC_Typ
                                                                    ((FStar_Reflection_Derived.type_of_binder
                                                                    b), [],
                                                                    Prims.int_zero))
                                                                    | 
                                                                    uu___5 ->
                                                                    FStar_Pervasives_Native.None))))
                                                       uu___3))) uu___2))))
                          uu___1))) uu___)
let (convert_ctrl_flag :
  FStar_Tactics_Types.ctrl_flag -> FStar_Tactics_Types.ctrl_flag) =
  fun flag ->
    match flag with
    | FStar_Tactics_Types.Continue -> FStar_Tactics_Types.Continue
    | FStar_Tactics_Types.Skip -> FStar_Tactics_Types.Continue
    | FStar_Tactics_Types.Abort -> FStar_Tactics_Types.Abort
type 'a explorer =
  'a ->
    FStar_InteractiveHelpers_Base.genv ->
      (FStar_InteractiveHelpers_Base.genv * FStar_Reflection_Data.term_view)
        Prims.list ->
        typ_or_comp FStar_Pervasives_Native.option ->
          FStar_Reflection_Data.term_view ->
            (('a * FStar_Tactics_Types.ctrl_flag), unit)
              FStar_Tactics_Effect.tac_repr
let bind_expl :
  'a .
    'a ->
      ('a ->
         (('a * FStar_Tactics_Types.ctrl_flag), unit)
           FStar_Tactics_Effect.tac_repr)
        ->
        ('a ->
           (('a * FStar_Tactics_Types.ctrl_flag), unit)
             FStar_Tactics_Effect.tac_repr)
          ->
          (('a * FStar_Tactics_Types.ctrl_flag), unit)
            FStar_Tactics_Effect.tac_repr
  =
  fun x ->
    fun f1 ->
      fun f2 ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Range.mk_range "FStar.InteractiveHelpers.ExploreTerm.fst"
             (Prims.of_int (435)) (Prims.of_int (18)) (Prims.of_int (435))
             (Prims.of_int (22)))
          (FStar_Range.mk_range "FStar.InteractiveHelpers.ExploreTerm.fst"
             (Prims.of_int (435)) (Prims.of_int (2)) (Prims.of_int (438))
             (Prims.of_int (34))) (Obj.magic (f1 x))
          (fun uu___ ->
             (fun uu___ ->
                match uu___ with
                | (x1, flag1) ->
                    if flag1 = FStar_Tactics_Types.Continue
                    then Obj.magic (Obj.repr (f2 x1))
                    else
                      Obj.magic
                        (Obj.repr
                           (FStar_Tactics_Effect.lift_div_tac
                              (fun uu___2 -> (x1, (convert_ctrl_flag flag1))))))
               uu___)
let rec (explore_term :
  Prims.bool ->
    Prims.bool ->
      unit ->
        Obj.t explorer ->
          Obj.t ->
            FStar_InteractiveHelpers_Base.genv ->
              (FStar_InteractiveHelpers_Base.genv *
                FStar_Reflection_Data.term_view) Prims.list ->
                typ_or_comp FStar_Pervasives_Native.option ->
                  FStar_Reflection_Types.term ->
                    ((Obj.t * FStar_Tactics_Types.ctrl_flag), unit)
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
                    FStar_Tactics_Effect.tac_bind
                      (FStar_Range.mk_range
                         "FStar.InteractiveHelpers.ExploreTerm.fst"
                         (Prims.of_int (467)) (Prims.of_int (2))
                         (Prims.of_int (467)) (Prims.of_int (85)))
                      (FStar_Range.mk_range
                         "FStar.InteractiveHelpers.ExploreTerm.fst"
                         (Prims.of_int (468)) (Prims.of_int (2))
                         (Prims.of_int (547)) (Prims.of_int (33)))
                      (Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Range.mk_range
                               "FStar.InteractiveHelpers.ExploreTerm.fst"
                               (Prims.of_int (467)) (Prims.of_int (16))
                               (Prims.of_int (467)) (Prims.of_int (85)))
                            (FStar_Range.mk_range
                               "FStar.InteractiveHelpers.ExploreTerm.fst"
                               (Prims.of_int (467)) (Prims.of_int (2))
                               (Prims.of_int (467)) (Prims.of_int (85)))
                            (Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Range.mk_range
                                     "FStar.InteractiveHelpers.ExploreTerm.fst"
                                     (Prims.of_int (467)) (Prims.of_int (39))
                                     (Prims.of_int (467)) (Prims.of_int (84)))
                                  (FStar_Range.mk_range "prims.fst"
                                     (Prims.of_int (590)) (Prims.of_int (19))
                                     (Prims.of_int (590)) (Prims.of_int (31)))
                                  (Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Range.mk_range
                                           "FStar.InteractiveHelpers.ExploreTerm.fst"
                                           (Prims.of_int (467))
                                           (Prims.of_int (39))
                                           (Prims.of_int (467))
                                           (Prims.of_int (56)))
                                        (FStar_Range.mk_range
                                           "FStar.InteractiveHelpers.ExploreTerm.fst"
                                           (Prims.of_int (467))
                                           (Prims.of_int (39))
                                           (Prims.of_int (467))
                                           (Prims.of_int (84)))
                                        (Obj.magic
                                           (FStar_InteractiveHelpers_Base.term_construct
                                              t0))
                                        (fun uu___ ->
                                           (fun uu___ ->
                                              Obj.magic
                                                (FStar_Tactics_Effect.tac_bind
                                                   (FStar_Range.mk_range
                                                      "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                      (Prims.of_int (467))
                                                      (Prims.of_int (59))
                                                      (Prims.of_int (467))
                                                      (Prims.of_int (84)))
                                                   (FStar_Range.mk_range
                                                      "prims.fst"
                                                      (Prims.of_int (590))
                                                      (Prims.of_int (19))
                                                      (Prims.of_int (590))
                                                      (Prims.of_int (31)))
                                                   (Obj.magic
                                                      (FStar_Tactics_Effect.tac_bind
                                                         (FStar_Range.mk_range
                                                            "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                            (Prims.of_int (467))
                                                            (Prims.of_int (67))
                                                            (Prims.of_int (467))
                                                            (Prims.of_int (84)))
                                                         (FStar_Range.mk_range
                                                            "prims.fst"
                                                            (Prims.of_int (590))
                                                            (Prims.of_int (19))
                                                            (Prims.of_int (590))
                                                            (Prims.of_int (31)))
                                                         (Obj.magic
                                                            (FStar_Tactics_Builtins.term_to_string
                                                               t0))
                                                         (fun uu___1 ->
                                                            FStar_Tactics_Effect.lift_div_tac
                                                              (fun uu___2 ->
                                                                 Prims.strcat
                                                                   ":\n"
                                                                   uu___1))))
                                                   (fun uu___1 ->
                                                      FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___2 ->
                                                           Prims.strcat uu___
                                                             uu___1)))) uu___)))
                                  (fun uu___ ->
                                     FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___1 ->
                                          Prims.strcat "[> explore_term: "
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
                                 (FStar_Range.mk_range
                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                    (Prims.of_int (468)) (Prims.of_int (12))
                                    (Prims.of_int (468)) (Prims.of_int (22)))
                                 (FStar_Range.mk_range
                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                    (Prims.of_int (469)) (Prims.of_int (2))
                                    (Prims.of_int (547)) (Prims.of_int (33)))
                                 (Obj.magic
                                    (FStar_Tactics_Builtins.inspect t0))
                                 (fun uu___1 ->
                                    (fun tv0 ->
                                       Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Range.mk_range
                                               "FStar.InteractiveHelpers.ExploreTerm.fst"
                                               (Prims.of_int (469))
                                               (Prims.of_int (17))
                                               (Prims.of_int (469))
                                               (Prims.of_int (35)))
                                            (FStar_Range.mk_range
                                               "FStar.InteractiveHelpers.ExploreTerm.fst"
                                               (Prims.of_int (469))
                                               (Prims.of_int (2))
                                               (Prims.of_int (547))
                                               (Prims.of_int (33)))
                                            (Obj.magic (f x ge0 pl0 c0 tv0))
                                            (fun uu___1 ->
                                               (fun uu___1 ->
                                                  match uu___1 with
                                                  | (x0, flag) ->
                                                      Obj.magic
                                                        (FStar_Tactics_Effect.tac_bind
                                                           (FStar_Range.mk_range
                                                              "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                              (Prims.of_int (470))
                                                              (Prims.of_int (23))
                                                              (Prims.of_int (470))
                                                              (Prims.of_int (25)))
                                                           (FStar_Range.mk_range
                                                              "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                              (Prims.of_int (471))
                                                              (Prims.of_int (2))
                                                              (Prims.of_int (547))
                                                              (Prims.of_int (33)))
                                                           (FStar_Tactics_Effect.lift_div_tac
                                                              (fun uu___2 ->
                                                                 (ge0, tv0)
                                                                 :: pl0))
                                                           (fun uu___2 ->
                                                              (fun pl1 ->
                                                                 if
                                                                   flag =
                                                                    FStar_Tactics_Types.Continue
                                                                 then
                                                                   Obj.magic
                                                                    (Obj.repr
                                                                    (match tv0
                                                                    with
                                                                    | 
                                                                    FStar_Reflection_Data.Tv_Var
                                                                    uu___2 ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    (x0,
                                                                    FStar_Tactics_Types.Continue)))
                                                                    | 
                                                                    FStar_Reflection_Data.Tv_BVar
                                                                    uu___2 ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    (x0,
                                                                    FStar_Tactics_Types.Continue)))
                                                                    | 
                                                                    FStar_Reflection_Data.Tv_FVar
                                                                    uu___2 ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    (x0,
                                                                    FStar_Tactics_Types.Continue)))
                                                                    | 
                                                                    FStar_Reflection_Data.Tv_App
                                                                    (hd,
                                                                    (a1,
                                                                    qual)) ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (478))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (478))
                                                                    (Prims.of_int (51)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (479))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (486))
                                                                    (Prims.of_int (38)))
                                                                    (Obj.magic
                                                                    (safe_arg_typ_or_comp
                                                                    dbg
                                                                    ge0.FStar_InteractiveHelpers_Base.env
                                                                    hd))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun a_c
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (479))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (480))
                                                                    (Prims.of_int (64)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (481))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (486))
                                                                    (Prims.of_int (38)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (479))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (480))
                                                                    (Prims.of_int (64)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (479))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (480))
                                                                    (Prims.of_int (64)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (480))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (480))
                                                                    (Prims.of_int (63)))
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.option_to_string
                                                                    typ_or_comp_to_string
                                                                    a_c))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Prims.strcat
                                                                    "Tv_App: updated target typ_or_comp to:\n"
                                                                    uu___2))))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    uu___2))
                                                                    uu___2)))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (481))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (481))
                                                                    (Prims.of_int (61)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (481))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (486))
                                                                    (Prims.of_int (38)))
                                                                    (Obj.magic
                                                                    (explore_term
                                                                    dbg dfs
                                                                    () f x0
                                                                    ge0 pl1
                                                                    a_c a1))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    (x1,
                                                                    flag1) ->
                                                                    if
                                                                    flag1 =
                                                                    FStar_Tactics_Types.Continue
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
                                                                    uu___5 ->
                                                                    (x1,
                                                                    (convert_ctrl_flag
                                                                    flag1))))))
                                                                    uu___3)))
                                                                    uu___2)))
                                                                    uu___2))
                                                                    | 
                                                                    FStar_Reflection_Data.Tv_Abs
                                                                    (br,
                                                                    body) ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (488))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (488))
                                                                    (Prims.of_int (50)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (489))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (490))
                                                                    (Prims.of_int (47)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.genv_push_binder
                                                                    ge0 br
                                                                    false
                                                                    FStar_Pervasives_Native.None))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun ge1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (489))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (489))
                                                                    (Prims.of_int (55)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (490))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (490))
                                                                    (Prims.of_int (47)))
                                                                    (Obj.magic
                                                                    (abs_update_opt_typ_or_comp
                                                                    br c0
                                                                    ge1.FStar_InteractiveHelpers_Base.env))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun c1
                                                                    ->
                                                                    Obj.magic
                                                                    (explore_term
                                                                    dbg dfs
                                                                    () f x0
                                                                    ge1 pl1
                                                                    c1 body))
                                                                    uu___2)))
                                                                    uu___2))
                                                                    | 
                                                                    FStar_Reflection_Data.Tv_Arrow
                                                                    (br, c01)
                                                                    ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    (x0,
                                                                    FStar_Tactics_Types.Continue)))
                                                                    | 
                                                                    FStar_Reflection_Data.Tv_Type
                                                                    uu___2 ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    (x0,
                                                                    FStar_Tactics_Types.Continue)))
                                                                    | 
                                                                    FStar_Reflection_Data.Tv_Refine
                                                                    (bv,
                                                                    sort,
                                                                    ref) ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (494))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (494))
                                                                    (Prims.of_int (29)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (495))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (499))
                                                                    (Prims.of_int (38)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Reflection_Builtins.inspect_bv
                                                                    bv))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun bvv
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (495))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (495))
                                                                    (Prims.of_int (65)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (495))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (499))
                                                                    (Prims.of_int (38)))
                                                                    (Obj.magic
                                                                    (explore_term
                                                                    dbg dfs
                                                                    () f x0
                                                                    ge0 pl1
                                                                    FStar_Pervasives_Native.None
                                                                    sort))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    match uu___2
                                                                    with
                                                                    | 
                                                                    (x1,
                                                                    flag1) ->
                                                                    if
                                                                    flag1 =
                                                                    FStar_Tactics_Types.Continue
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (497))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (497))
                                                                    (Prims.of_int (53)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (498))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (498))
                                                                    (Prims.of_int (50)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.genv_push_bv
                                                                    ge0 bv
                                                                    sort
                                                                    false
                                                                    FStar_Pervasives_Native.None))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun ge1
                                                                    ->
                                                                    Obj.magic
                                                                    (explore_term
                                                                    dbg dfs
                                                                    () f x1
                                                                    ge1 pl1
                                                                    FStar_Pervasives_Native.None
                                                                    ref))
                                                                    uu___3)))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    (x1,
                                                                    (convert_ctrl_flag
                                                                    flag1))))))
                                                                    uu___2)))
                                                                    uu___2))
                                                                    | 
                                                                    FStar_Reflection_Data.Tv_Const
                                                                    uu___2 ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    (x0,
                                                                    FStar_Tactics_Types.Continue)))
                                                                    | 
                                                                    FStar_Reflection_Data.Tv_Uvar
                                                                    (uu___2,
                                                                    uu___3)
                                                                    ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    (x0,
                                                                    FStar_Tactics_Types.Continue)))
                                                                    | 
                                                                    FStar_Reflection_Data.Tv_Let
                                                                    (recf,
                                                                    attrs,
                                                                    bv, ty,
                                                                    def,
                                                                    body) ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (506))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (506))
                                                                    (Prims.of_int (39)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (507))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (513))
                                                                    (Prims.of_int (30)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Pervasives_Native.Some
                                                                    (TC_Typ
                                                                    (ty, [],
                                                                    Prims.int_zero))))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    def_c ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (507))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (507))
                                                                    (Prims.of_int (68)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (509))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (513))
                                                                    (Prims.of_int (30)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    fun x1 ->
                                                                    explore_term
                                                                    dbg dfs
                                                                    () f x1
                                                                    ge0 pl1
                                                                    def_c def))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    explore_def
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (509))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (509))
                                                                    (Prims.of_int (55)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (510))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (513))
                                                                    (Prims.of_int (30)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.genv_push_bv
                                                                    ge0 bv ty
                                                                    false
                                                                    (FStar_Pervasives_Native.Some
                                                                    def)))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun ge1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (510))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (510))
                                                                    (Prims.of_int (67)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (512))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (513))
                                                                    (Prims.of_int (30)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    fun x1 ->
                                                                    explore_term
                                                                    dbg dfs
                                                                    () f x1
                                                                    ge1 pl1
                                                                    c0 body))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    explore_next
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (512))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (512))
                                                                    (Prims.of_int (93)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (512))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (513))
                                                                    (Prims.of_int (30)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    if dfs
                                                                    then
                                                                    (explore_next,
                                                                    explore_def)
                                                                    else
                                                                    (explore_def,
                                                                    explore_next)))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    match uu___2
                                                                    with
                                                                    | 
                                                                    (expl1,
                                                                    expl2) ->
                                                                    Obj.magic
                                                                    (bind_expl
                                                                    x0 expl1
                                                                    expl2))
                                                                    uu___2)))
                                                                    uu___2)))
                                                                    uu___2)))
                                                                    uu___2)))
                                                                    uu___2))
                                                                    | 
                                                                    FStar_Reflection_Data.Tv_Match
                                                                    (scrutinee,
                                                                    _ret_opt,
                                                                    branches)
                                                                    ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (517))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (527))
                                                                    (Prims.of_int (21)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (530))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (533))
                                                                    (Prims.of_int (42)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    fun
                                                                    x_flag ->
                                                                    fun br ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (517))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (517))
                                                                    (Prims.of_int (29)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (517))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (527))
                                                                    (Prims.of_int (21)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    x_flag))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    (x01,
                                                                    flag1) ->
                                                                    if
                                                                    flag1 =
                                                                    FStar_Tactics_Types.Continue
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (519))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (519))
                                                                    (Prims.of_int (35)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (519))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (525))
                                                                    (Prims.of_int (42)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    br))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    (pat,
                                                                    branch_body)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (521))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (521))
                                                                    (Prims.of_int (70)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (521))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (525))
                                                                    (Prims.of_int (42)))
                                                                    (Obj.magic
                                                                    (explore_pattern
                                                                    dbg dfs
                                                                    () f x01
                                                                    ge0 pat))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    match uu___5
                                                                    with
                                                                    | 
                                                                    (ge1, x1,
                                                                    flag11)
                                                                    ->
                                                                    if
                                                                    flag11 =
                                                                    FStar_Tactics_Types.Continue
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
                                                                    uu___7 ->
                                                                    (x1,
                                                                    (convert_ctrl_flag
                                                                    flag11))))))
                                                                    uu___5)))
                                                                    uu___4)))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    (x01,
                                                                    flag1)))))
                                                                    uu___3)))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    explore_branch
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (530))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (530))
                                                                    (Prims.of_int (58)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (531))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (533))
                                                                    (Prims.of_int (42)))
                                                                    (Obj.magic
                                                                    (safe_typ_or_comp
                                                                    dbg
                                                                    ge0.FStar_InteractiveHelpers_Base.env
                                                                    scrutinee))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    scrut_c
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (531))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (531))
                                                                    (Prims.of_int (69)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (533))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (533))
                                                                    (Prims.of_int (42)))
                                                                    (Obj.magic
                                                                    (explore_term
                                                                    dbg dfs
                                                                    () f x0
                                                                    ge0 pl1
                                                                    scrut_c
                                                                    scrutinee))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun x1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Util.fold_left
                                                                    explore_branch
                                                                    x1
                                                                    branches))
                                                                    uu___2)))
                                                                    uu___2)))
                                                                    uu___2))
                                                                    | 
                                                                    FStar_Reflection_Data.Tv_AscribedT
                                                                    (e, ty,
                                                                    tac,
                                                                    uu___2)
                                                                    ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (535))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (535))
                                                                    (Prims.of_int (36)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (536))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (539))
                                                                    (Prims.of_int (37)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Pervasives_Native.Some
                                                                    (TC_Typ
                                                                    (ty, [],
                                                                    Prims.int_zero))))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun c1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (536))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (536))
                                                                    (Prims.of_int (65)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (536))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (539))
                                                                    (Prims.of_int (37)))
                                                                    (Obj.magic
                                                                    (explore_term
                                                                    dbg dfs
                                                                    () f x0
                                                                    ge0 pl1
                                                                    FStar_Pervasives_Native.None
                                                                    ty))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    (x1,
                                                                    flag1) ->
                                                                    if
                                                                    flag1 =
                                                                    FStar_Tactics_Types.Continue
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
                                                                    uu___5 ->
                                                                    (x1,
                                                                    (convert_ctrl_flag
                                                                    flag1))))))
                                                                    uu___3)))
                                                                    uu___3))
                                                                    | 
                                                                    FStar_Reflection_Data.Tv_AscribedC
                                                                    (e, c1,
                                                                    tac,
                                                                    uu___2)
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
                                                                    uu___2 ->
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    (x0,
                                                                    FStar_Tactics_Types.Continue)))))
                                                                 else
                                                                   Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    (x0,
                                                                    (convert_ctrl_flag
                                                                    flag))))))
                                                                uu___2)))
                                                 uu___1))) uu___1))) uu___)
and (explore_pattern :
  Prims.bool ->
    Prims.bool ->
      unit ->
        Obj.t explorer ->
          Obj.t ->
            FStar_InteractiveHelpers_Base.genv ->
              FStar_Reflection_Data.pattern ->
                ((FStar_InteractiveHelpers_Base.genv * Obj.t *
                   FStar_Tactics_Types.ctrl_flag),
                  unit) FStar_Tactics_Effect.tac_repr)
  =
  fun dbg ->
    fun dfs ->
      fun a ->
        fun f ->
          fun x ->
            fun ge0 ->
              fun pat ->
                FStar_Tactics_Effect.tac_bind
                  (FStar_Range.mk_range
                     "FStar.InteractiveHelpers.ExploreTerm.fst"
                     (Prims.of_int (550)) (Prims.of_int (2))
                     (Prims.of_int (550)) (Prims.of_int (39)))
                  (FStar_Range.mk_range
                     "FStar.InteractiveHelpers.ExploreTerm.fst"
                     (Prims.of_int (551)) (Prims.of_int (2))
                     (Prims.of_int (567)) (Prims.of_int (38)))
                  (Obj.magic
                     (FStar_InteractiveHelpers_Base.print_dbg dbg
                        "[> explore_pattern:"))
                  (fun uu___ ->
                     (fun uu___ ->
                        match pat with
                        | FStar_Reflection_Data.Pat_Constant uu___1 ->
                            Obj.magic
                              (Obj.repr
                                 (FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___2 ->
                                       (ge0, x, FStar_Tactics_Types.Continue))))
                        | FStar_Reflection_Data.Pat_Cons (fv, us, patterns)
                            ->
                            Obj.magic
                              (Obj.repr
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Range.mk_range
                                       "FStar.InteractiveHelpers.ExploreTerm.fst"
                                       (Prims.of_int (555))
                                       (Prims.of_int (6))
                                       (Prims.of_int (561))
                                       (Prims.of_int (20)))
                                    (FStar_Range.mk_range
                                       "FStar.InteractiveHelpers.ExploreTerm.fst"
                                       (Prims.of_int (563))
                                       (Prims.of_int (4))
                                       (Prims.of_int (563))
                                       (Prims.of_int (53)))
                                    (FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___1 ->
                                          fun ge_x_flag ->
                                            fun pat1 ->
                                              FStar_Tactics_Effect.tac_bind
                                                (FStar_Range.mk_range
                                                   "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                   (Prims.of_int (555))
                                                   (Prims.of_int (25))
                                                   (Prims.of_int (555))
                                                   (Prims.of_int (34)))
                                                (FStar_Range.mk_range
                                                   "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                   (Prims.of_int (555))
                                                   (Prims.of_int (6))
                                                   (Prims.of_int (561))
                                                   (Prims.of_int (20)))
                                                (FStar_Tactics_Effect.lift_div_tac
                                                   (fun uu___2 -> ge_x_flag))
                                                (fun uu___2 ->
                                                   (fun uu___2 ->
                                                      match uu___2 with
                                                      | (ge01, x1, flag) ->
                                                          Obj.magic
                                                            (FStar_Tactics_Effect.tac_bind
                                                               (FStar_Range.mk_range
                                                                  "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                  (Prims.of_int (556))
                                                                  (Prims.of_int (20))
                                                                  (Prims.of_int (556))
                                                                  (Prims.of_int (23)))
                                                               (FStar_Range.mk_range
                                                                  "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                  (Prims.of_int (556))
                                                                  (Prims.of_int (6))
                                                                  (Prims.of_int (561))
                                                                  (Prims.of_int (20)))
                                                               (FStar_Tactics_Effect.lift_div_tac
                                                                  (fun uu___3
                                                                    -> pat1))
                                                               (fun uu___3 ->
                                                                  (fun uu___3
                                                                    ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    (pat11,
                                                                    uu___4)
                                                                    ->
                                                                    if
                                                                    flag =
                                                                    FStar_Tactics_Types.Continue
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
                                                                    uu___6 ->
                                                                    (ge01,
                                                                    x1, flag)))))
                                                                    uu___3)))
                                                     uu___2)))
                                    (fun uu___1 ->
                                       (fun explore_pat ->
                                          Obj.magic
                                            (FStar_Tactics_Util.fold_left
                                               explore_pat
                                               (ge0, x,
                                                 FStar_Tactics_Types.Continue)
                                               patterns)) uu___1)))
                        | FStar_Reflection_Data.Pat_Var (bv, st) ->
                            Obj.magic
                              (Obj.repr
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Range.mk_range
                                       "FStar.InteractiveHelpers.ExploreTerm.fst"
                                       (Prims.of_int (565))
                                       (Prims.of_int (14))
                                       (Prims.of_int (565))
                                       (Prims.of_int (56)))
                                    (FStar_Range.mk_range
                                       "FStar.InteractiveHelpers.ExploreTerm.fst"
                                       (Prims.of_int (566))
                                       (Prims.of_int (4))
                                       (Prims.of_int (566))
                                       (Prims.of_int (20)))
                                    (Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Range.mk_range
                                             "FStar.InteractiveHelpers.ExploreTerm.fst"
                                             (Prims.of_int (565))
                                             (Prims.of_int (34))
                                             (Prims.of_int (565))
                                             (Prims.of_int (45)))
                                          (FStar_Range.mk_range
                                             "FStar.InteractiveHelpers.ExploreTerm.fst"
                                             (Prims.of_int (565))
                                             (Prims.of_int (14))
                                             (Prims.of_int (565))
                                             (Prims.of_int (56)))
                                          (Obj.magic
                                             (FStar_Tactics_Builtins.unseal
                                                st))
                                          (fun uu___1 ->
                                             (fun uu___1 ->
                                                Obj.magic
                                                  (FStar_InteractiveHelpers_Base.genv_push_bv
                                                     ge0 bv uu___1 false
                                                     FStar_Pervasives_Native.None))
                                               uu___1)))
                                    (fun ge1 ->
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___1 ->
                                            (ge1, x,
                                              FStar_Tactics_Types.Continue)))))
                        | FStar_Reflection_Data.Pat_Wild (bv, st) ->
                            Obj.magic
                              (Obj.repr
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Range.mk_range
                                       "FStar.InteractiveHelpers.ExploreTerm.fst"
                                       (Prims.of_int (565))
                                       (Prims.of_int (14))
                                       (Prims.of_int (565))
                                       (Prims.of_int (56)))
                                    (FStar_Range.mk_range
                                       "FStar.InteractiveHelpers.ExploreTerm.fst"
                                       (Prims.of_int (566))
                                       (Prims.of_int (4))
                                       (Prims.of_int (566))
                                       (Prims.of_int (20)))
                                    (Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Range.mk_range
                                             "FStar.InteractiveHelpers.ExploreTerm.fst"
                                             (Prims.of_int (565))
                                             (Prims.of_int (34))
                                             (Prims.of_int (565))
                                             (Prims.of_int (45)))
                                          (FStar_Range.mk_range
                                             "FStar.InteractiveHelpers.ExploreTerm.fst"
                                             (Prims.of_int (565))
                                             (Prims.of_int (14))
                                             (Prims.of_int (565))
                                             (Prims.of_int (56)))
                                          (Obj.magic
                                             (FStar_Tactics_Builtins.unseal
                                                st))
                                          (fun uu___1 ->
                                             (fun uu___1 ->
                                                Obj.magic
                                                  (FStar_InteractiveHelpers_Base.genv_push_bv
                                                     ge0 bv uu___1 false
                                                     FStar_Pervasives_Native.None))
                                               uu___1)))
                                    (fun ge1 ->
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___1 ->
                                            (ge1, x,
                                              FStar_Tactics_Types.Continue)))))
                        | FStar_Reflection_Data.Pat_Dot_Term uu___1 ->
                            Obj.magic
                              (Obj.repr
                                 (FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___2 ->
                                       (ge0, x, FStar_Tactics_Types.Continue)))))
                       uu___)
let (free_in :
  FStar_Reflection_Types.term ->
    (FStar_Reflection_Types.bv Prims.list, unit)
      FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Range.mk_range "FStar.InteractiveHelpers.ExploreTerm.fst"
         (Prims.of_int (574)) (Prims.of_int (4)) (Prims.of_int (574))
         (Prims.of_int (35)))
      (FStar_Range.mk_range "FStar.InteractiveHelpers.ExploreTerm.fst"
         (Prims.of_int (576)) (Prims.of_int (2)) (Prims.of_int (593))
         (Prims.of_int (75)))
      (FStar_Tactics_Effect.lift_div_tac
         (fun uu___ ->
            fun bv1 ->
              fun bv2 ->
                FStar_Tactics_Effect.tac_bind
                  (FStar_Range.mk_range
                     "FStar.InteractiveHelpers.ExploreTerm.fst"
                     (Prims.of_int (574)) (Prims.of_int (4))
                     (Prims.of_int (574)) (Prims.of_int (18)))
                  (FStar_Range.mk_range
                     "FStar.InteractiveHelpers.ExploreTerm.fst"
                     (Prims.of_int (574)) (Prims.of_int (4))
                     (Prims.of_int (574)) (Prims.of_int (35)))
                  (Obj.magic (FStar_Tactics_Derived.name_of_bv bv1))
                  (fun uu___1 ->
                     (fun uu___1 ->
                        Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Range.mk_range
                                "FStar.InteractiveHelpers.ExploreTerm.fst"
                                (Prims.of_int (574)) (Prims.of_int (21))
                                (Prims.of_int (574)) (Prims.of_int (35)))
                             (FStar_Range.mk_range
                                "FStar.InteractiveHelpers.ExploreTerm.fst"
                                (Prims.of_int (574)) (Prims.of_int (4))
                                (Prims.of_int (574)) (Prims.of_int (35)))
                             (Obj.magic
                                (FStar_Tactics_Derived.name_of_bv bv2))
                             (fun uu___2 ->
                                FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___3 -> uu___1 = uu___2)))) uu___1)))
      (fun uu___ ->
         (fun same_name ->
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Range.mk_range
                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                    (Prims.of_int (579)) (Prims.of_int (4))
                    (Prims.of_int (589)) (Prims.of_int (23)))
                 (FStar_Range.mk_range
                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                    (Prims.of_int (591)) (Prims.of_int (2))
                    (Prims.of_int (593)) (Prims.of_int (75)))
                 (FStar_Tactics_Effect.lift_div_tac
                    (fun uu___5 ->
                       fun uu___4 ->
                         fun uu___3 ->
                           fun uu___2 ->
                             fun uu___1 ->
                               fun uu___ ->
                                 (fun uu___ ->
                                    fun fl ->
                                      fun ge ->
                                        fun pl ->
                                          fun c ->
                                            fun tv ->
                                              match tv with
                                              | FStar_Reflection_Data.Tv_Var
                                                  bv ->
                                                  Obj.magic
                                                    (Obj.repr
                                                       (FStar_Tactics_Effect.tac_bind
                                                          (FStar_Range.mk_range
                                                             "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                             (Prims.of_int (582))
                                                             (Prims.of_int (18))
                                                             (Prims.of_int (582))
                                                             (Prims.of_int (55)))
                                                          (FStar_Range.mk_range
                                                             "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                             (Prims.of_int (582))
                                                             (Prims.of_int (12))
                                                             (Prims.of_int (587))
                                                             (Prims.of_int (30)))
                                                          (Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Range.mk_range
                                                                   "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                   (Prims.of_int (582))
                                                                   (Prims.of_int (40))
                                                                   (Prims.of_int (582))
                                                                   (Prims.of_int (55)))
                                                                (FStar_Range.mk_range
                                                                   "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                   (Prims.of_int (582))
                                                                   (Prims.of_int (18))
                                                                   (Prims.of_int (582))
                                                                   (Prims.of_int (55)))
                                                                (Obj.magic
                                                                   (FStar_Tactics_Derived.name_of_bv
                                                                    bv))
                                                                (fun uu___1
                                                                   ->
                                                                   (fun
                                                                    uu___1 ->
                                                                    Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.genv_get_from_name
                                                                    ge uu___1))
                                                                    uu___1)))
                                                          (fun uu___1 ->
                                                             (fun uu___1 ->
                                                                match uu___1
                                                                with
                                                                | FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (585))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (585))
                                                                    (Prims.of_int (76)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (586))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (586))
                                                                    (Prims.of_int (21)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (585))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (585))
                                                                    (Prims.of_int (54)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (585))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (585))
                                                                    (Prims.of_int (76)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Util.tryFind
                                                                    (same_name
                                                                    bv) fl))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    if uu___2
                                                                    then fl
                                                                    else bv
                                                                    :: fl))))
                                                                    (fun fl'
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fl',
                                                                    FStar_Tactics_Types.Continue)))))
                                                                | FStar_Pervasives_Native.Some
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fl,
                                                                    FStar_Tactics_Types.Continue)))))
                                                               uu___1)))
                                              | FStar_Reflection_Data.Tv_BVar
                                                  bv ->
                                                  Obj.magic
                                                    (Obj.repr
                                                       (FStar_Tactics_Effect.tac_bind
                                                          (FStar_Range.mk_range
                                                             "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                             (Prims.of_int (582))
                                                             (Prims.of_int (18))
                                                             (Prims.of_int (582))
                                                             (Prims.of_int (55)))
                                                          (FStar_Range.mk_range
                                                             "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                             (Prims.of_int (582))
                                                             (Prims.of_int (12))
                                                             (Prims.of_int (587))
                                                             (Prims.of_int (30)))
                                                          (Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Range.mk_range
                                                                   "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                   (Prims.of_int (582))
                                                                   (Prims.of_int (40))
                                                                   (Prims.of_int (582))
                                                                   (Prims.of_int (55)))
                                                                (FStar_Range.mk_range
                                                                   "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                   (Prims.of_int (582))
                                                                   (Prims.of_int (18))
                                                                   (Prims.of_int (582))
                                                                   (Prims.of_int (55)))
                                                                (Obj.magic
                                                                   (FStar_Tactics_Derived.name_of_bv
                                                                    bv))
                                                                (fun uu___1
                                                                   ->
                                                                   (fun
                                                                    uu___1 ->
                                                                    Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.genv_get_from_name
                                                                    ge uu___1))
                                                                    uu___1)))
                                                          (fun uu___1 ->
                                                             (fun uu___1 ->
                                                                match uu___1
                                                                with
                                                                | FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (585))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (585))
                                                                    (Prims.of_int (76)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (586))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (586))
                                                                    (Prims.of_int (21)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (585))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (585))
                                                                    (Prims.of_int (54)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                                    (Prims.of_int (585))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (585))
                                                                    (Prims.of_int (76)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Util.tryFind
                                                                    (same_name
                                                                    bv) fl))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    if uu___2
                                                                    then fl
                                                                    else bv
                                                                    :: fl))))
                                                                    (fun fl'
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fl',
                                                                    FStar_Tactics_Types.Continue)))))
                                                                | FStar_Pervasives_Native.Some
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fl,
                                                                    FStar_Tactics_Types.Continue)))))
                                                               uu___1)))
                                              | uu___1 ->
                                                  Obj.magic
                                                    (Obj.repr
                                                       (FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___2 ->
                                                             (fl,
                                                               FStar_Tactics_Types.Continue)))))
                                   uu___5 uu___4 uu___3 uu___2 uu___1 uu___))
                 (fun uu___ ->
                    (fun update_free ->
                       Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Range.mk_range
                               "FStar.InteractiveHelpers.ExploreTerm.fst"
                               (Prims.of_int (591)) (Prims.of_int (10))
                               (Prims.of_int (591)) (Prims.of_int (20)))
                            (FStar_Range.mk_range
                               "FStar.InteractiveHelpers.ExploreTerm.fst"
                               (Prims.of_int (592)) (Prims.of_int (2))
                               (Prims.of_int (593)) (Prims.of_int (75)))
                            (Obj.magic (FStar_Tactics_Builtins.top_env ()))
                            (fun uu___ ->
                               (fun e ->
                                  Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Range.mk_range
                                          "FStar.InteractiveHelpers.ExploreTerm.fst"
                                          (Prims.of_int (592))
                                          (Prims.of_int (11))
                                          (Prims.of_int (592))
                                          (Prims.of_int (26)))
                                       (FStar_Range.mk_range
                                          "FStar.InteractiveHelpers.ExploreTerm.fst"
                                          (Prims.of_int (593))
                                          (Prims.of_int (2))
                                          (Prims.of_int (593))
                                          (Prims.of_int (75)))
                                       (FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___ ->
                                             FStar_InteractiveHelpers_Base.mk_genv
                                               e [] []))
                                       (fun uu___ ->
                                          (fun ge ->
                                             Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Range.mk_range
                                                     "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                     (Prims.of_int (593))
                                                     (Prims.of_int (15))
                                                     (Prims.of_int (593))
                                                     (Prims.of_int (75)))
                                                  (FStar_Range.mk_range
                                                     "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                     (Prims.of_int (593))
                                                     (Prims.of_int (2))
                                                     (Prims.of_int (593))
                                                     (Prims.of_int (75)))
                                                  (Obj.magic
                                                     (FStar_Tactics_Effect.tac_bind
                                                        (FStar_Range.mk_range
                                                           "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                           (Prims.of_int (593))
                                                           (Prims.of_int (20))
                                                           (Prims.of_int (593))
                                                           (Prims.of_int (74)))
                                                        (FStar_Range.mk_range
                                                           "FStar.InteractiveHelpers.ExploreTerm.fst"
                                                           (Prims.of_int (593))
                                                           (Prims.of_int (15))
                                                           (Prims.of_int (593))
                                                           (Prims.of_int (75)))
                                                        (Obj.magic
                                                           (explore_term
                                                              false false ()
                                                              (Obj.magic
                                                                 update_free)
                                                              (Obj.magic [])
                                                              ge []
                                                              FStar_Pervasives_Native.None
                                                              t))
                                                        (fun uu___ ->
                                                           FStar_Tactics_Effect.lift_div_tac
                                                             (fun uu___1 ->
                                                                FStar_Pervasives_Native.fst
                                                                  uu___))))
                                                  (fun uu___ ->
                                                     FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___1 ->
                                                          FStar_List_Tot_Base.rev
                                                            uu___)))) uu___)))
                                 uu___))) uu___))) uu___)
let (abs_free_in :
  FStar_InteractiveHelpers_Base.genv ->
    FStar_Reflection_Types.term ->
      ((FStar_Reflection_Types.bv * FStar_Reflection_Types.typ) Prims.list,
        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun ge ->
    fun t ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Range.mk_range "FStar.InteractiveHelpers.ExploreTerm.fst"
           (Prims.of_int (599)) (Prims.of_int (12)) (Prims.of_int (599))
           (Prims.of_int (21)))
        (FStar_Range.mk_range "FStar.InteractiveHelpers.ExploreTerm.fst"
           (Prims.of_int (600)) (Prims.of_int (2)) (Prims.of_int (607))
           (Prims.of_int (9))) (Obj.magic (free_in t))
        (fun fvl ->
           FStar_Tactics_Effect.lift_div_tac
             (fun uu___ ->
                FStar_List_Tot_Base.concatMap
                  (fun uu___1 ->
                     match uu___1 with
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
    FStar_Reflection_Types.term ->
      (FStar_Reflection_Types.bv Prims.list, unit)
        FStar_Tactics_Effect.tac_repr)
  =
  fun ge ->
    fun t ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Range.mk_range "FStar.InteractiveHelpers.ExploreTerm.fst"
           (Prims.of_int (612)) (Prims.of_int (12)) (Prims.of_int (612))
           (Prims.of_int (21)))
        (FStar_Range.mk_range "FStar.InteractiveHelpers.ExploreTerm.fst"
           (Prims.of_int (613)) (Prims.of_int (2)) (Prims.of_int (613))
           (Prims.of_int (54))) (Obj.magic (free_in t))
        (fun fvl ->
           FStar_Tactics_Effect.lift_div_tac
             (fun uu___ ->
                FStar_List_Tot_Base.filter
                  (fun bv ->
                     FStar_InteractiveHelpers_Base.bv_is_shadowed ge bv) fvl))
let (term_has_shadowed_variables :
  FStar_InteractiveHelpers_Base.genv ->
    FStar_Reflection_Types.term ->
      (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun ge ->
    fun t ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Range.mk_range "FStar.InteractiveHelpers.ExploreTerm.fst"
           (Prims.of_int (618)) (Prims.of_int (12)) (Prims.of_int (618))
           (Prims.of_int (21)))
        (FStar_Range.mk_range "FStar.InteractiveHelpers.ExploreTerm.fst"
           (Prims.of_int (619)) (Prims.of_int (2)) (Prims.of_int (619))
           (Prims.of_int (50))) (Obj.magic (free_in t))
        (fun fvl ->
           FStar_Tactics_Effect.lift_div_tac
             (fun uu___ ->
                FStar_Pervasives_Native.uu___is_Some
                  (FStar_List_Tot_Base.tryFind
                     (FStar_InteractiveHelpers_Base.bv_is_shadowed ge) fvl)))