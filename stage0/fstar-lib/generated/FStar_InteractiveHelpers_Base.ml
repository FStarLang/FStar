open Prims
let (bv_eq :
  FStarC_Reflection_Types.bv -> FStarC_Reflection_Types.bv -> Prims.bool) =
  fun bv1 ->
    fun bv2 ->
      let bvv1 = FStarC_Reflection_V1_Builtins.inspect_bv bv1 in
      let bvv2 = FStarC_Reflection_V1_Builtins.inspect_bv bv2 in
      bvv1.FStarC_Reflection_V1_Data.bv_index =
        bvv2.FStarC_Reflection_V1_Data.bv_index
let (fv_eq :
  FStarC_Reflection_Types.fv -> FStarC_Reflection_Types.fv -> Prims.bool) =
  fun fv1 ->
    fun fv2 ->
      let n1 = FStarC_Reflection_V1_Builtins.inspect_fv fv1 in
      let n2 = FStarC_Reflection_V1_Builtins.inspect_fv fv2 in n1 = n2
let (fv_eq_name :
  FStarC_Reflection_Types.fv -> FStarC_Reflection_Types.name -> Prims.bool) =
  fun fv ->
    fun n -> let fvn = FStarC_Reflection_V1_Builtins.inspect_fv fv in fvn = n
let opt_apply :
  'a 'b .
    ('a -> 'b) ->
      'a FStar_Pervasives_Native.option -> 'b FStar_Pervasives_Native.option
  =
  fun f ->
    fun x ->
      match x with
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some x' ->
          FStar_Pervasives_Native.Some (f x')
let opt_tapply :
  'a 'b .
    ('a -> ('b, unit) FStar_Tactics_Effect.tac_repr) ->
      'a FStar_Pervasives_Native.option ->
        ('b FStar_Pervasives_Native.option, unit)
          FStar_Tactics_Effect.tac_repr
  =
  fun uu___1 ->
    fun uu___ ->
      (fun f ->
         fun x ->
           match x with
           | FStar_Pervasives_Native.None ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac
                       (fun uu___ -> FStar_Pervasives_Native.None)))
           | FStar_Pervasives_Native.Some x' ->
               Obj.magic
                 (Obj.repr
                    (let uu___ = f x' in
                     FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.InteractiveHelpers.Base.fst"
                                (Prims.of_int (42)) (Prims.of_int (20))
                                (Prims.of_int (42)) (Prims.of_int (26)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.InteractiveHelpers.Base.fst"
                                (Prims.of_int (42)) (Prims.of_int (15))
                                (Prims.of_int (42)) (Prims.of_int (26)))))
                       (Obj.magic uu___)
                       (fun uu___1 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___2 ->
                               FStar_Pervasives_Native.Some uu___1)))))
        uu___1 uu___
let option_to_string :
  'a .
    ('a -> (Prims.string, unit) FStar_Tactics_Effect.tac_repr) ->
      'a FStar_Pervasives_Native.option ->
        (Prims.string, unit) FStar_Tactics_Effect.tac_repr
  =
  fun uu___1 ->
    fun uu___ ->
      (fun f ->
         fun x ->
           match x with
           | FStar_Pervasives_Native.None ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> "None")))
           | FStar_Pervasives_Native.Some x' ->
               Obj.magic
                 (Obj.repr
                    (let uu___ =
                       let uu___1 = f x' in
                       FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.InteractiveHelpers.Base.fst"
                                  (Prims.of_int (48)) (Prims.of_int (26))
                                  (Prims.of_int (48)) (Prims.of_int (30)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Prims.fst"
                                  (Prims.of_int (611)) (Prims.of_int (19))
                                  (Prims.of_int (611)) (Prims.of_int (31)))))
                         (Obj.magic uu___1)
                         (fun uu___2 ->
                            FStar_Tactics_Effect.lift_div_tac
                              (fun uu___3 -> Prims.strcat uu___2 ")")) in
                     FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.InteractiveHelpers.Base.fst"
                                (Prims.of_int (48)) (Prims.of_int (26))
                                (Prims.of_int (48)) (Prims.of_int (36)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Prims.fst"
                                (Prims.of_int (611)) (Prims.of_int (19))
                                (Prims.of_int (611)) (Prims.of_int (31)))))
                       (Obj.magic uu___)
                       (fun uu___1 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___2 -> Prims.strcat "Some (" uu___1)))))
        uu___1 uu___
let opt_cons :
  'a . 'a FStar_Pervasives_Native.option -> 'a Prims.list -> 'a Prims.list =
  fun opt_x ->
    fun ls ->
      match opt_x with
      | FStar_Pervasives_Native.Some x -> x :: ls
      | FStar_Pervasives_Native.None -> ls
let list_to_string :
  'a .
    ('a -> (Prims.string, unit) FStar_Tactics_Effect.tac_repr) ->
      'a Prims.list -> (Prims.string, unit) FStar_Tactics_Effect.tac_repr
  =
  fun f ->
    fun ls ->
      let uu___ =
        FStar_Tactics_Util.fold_left
          (fun s ->
             fun x ->
               let uu___1 =
                 let uu___2 =
                   let uu___3 = f x in
                   FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.InteractiveHelpers.Base.fst"
                              (Prims.of_int (58)) (Prims.of_int (49))
                              (Prims.of_int (58)) (Prims.of_int (52)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Prims.fst"
                              (Prims.of_int (611)) (Prims.of_int (19))
                              (Prims.of_int (611)) (Prims.of_int (31)))))
                     (Obj.magic uu___3)
                     (fun uu___4 ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___5 -> Prims.strcat uu___4 ");")) in
                 FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.InteractiveHelpers.Base.fst"
                            (Prims.of_int (58)) (Prims.of_int (49))
                            (Prims.of_int (58)) (Prims.of_int (59)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Prims.fst"
                            (Prims.of_int (611)) (Prims.of_int (19))
                            (Prims.of_int (611)) (Prims.of_int (31)))))
                   (Obj.magic uu___2)
                   (fun uu___3 ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___4 -> Prims.strcat " (" uu___3)) in
               FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range
                          "FStar.InteractiveHelpers.Base.fst"
                          (Prims.of_int (58)) (Prims.of_int (42))
                          (Prims.of_int (58)) (Prims.of_int (59)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "Prims.fst" (Prims.of_int (611))
                          (Prims.of_int (19)) (Prims.of_int (611))
                          (Prims.of_int (31))))) (Obj.magic uu___1)
                 (fun uu___2 ->
                    FStar_Tactics_Effect.lift_div_tac
                      (fun uu___3 -> Prims.strcat s uu___2))) "[" ls in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.InteractiveHelpers.Base.fst"
                 (Prims.of_int (58)) (Prims.of_int (2)) (Prims.of_int (58))
                 (Prims.of_int (68)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Prims.fst" (Prims.of_int (611))
                 (Prims.of_int (19)) (Prims.of_int (611)) (Prims.of_int (31)))))
        (Obj.magic uu___)
        (fun uu___1 ->
           FStar_Tactics_Effect.lift_div_tac
             (fun uu___2 -> Prims.strcat uu___1 "]"))
let (mk_app_norm :
  FStarC_Reflection_Types.env ->
    FStarC_Reflection_Types.term ->
      FStarC_Reflection_Types.term Prims.list ->
        (FStarC_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun e ->
    fun t ->
      fun params ->
        let uu___ =
          Obj.magic
            (FStar_Tactics_Effect.lift_div_tac
               (fun uu___1 -> FStar_Reflection_V1_Derived.mk_e_app t params)) in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.InteractiveHelpers.Base.fst"
                   (Prims.of_int (65)) (Prims.of_int (11))
                   (Prims.of_int (65)) (Prims.of_int (28)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.InteractiveHelpers.Base.fst"
                   (Prims.of_int (65)) (Prims.of_int (31))
                   (Prims.of_int (67)) (Prims.of_int (4)))))
          (Obj.magic uu___)
          (fun uu___1 ->
             (fun t1 ->
                let uu___1 = FStarC_Tactics_V1_Builtins.norm_term_env e [] t1 in
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.InteractiveHelpers.Base.fst"
                              (Prims.of_int (66)) (Prims.of_int (11))
                              (Prims.of_int (66)) (Prims.of_int (32)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.InteractiveHelpers.Base.fst"
                              (Prims.of_int (66)) (Prims.of_int (6))
                              (Prims.of_int (66)) (Prims.of_int (8)))))
                     (Obj.magic uu___1)
                     (fun t2 ->
                        FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> t2))))
               uu___1)
let (opt_mk_app_norm :
  FStarC_Reflection_Types.env ->
    FStarC_Reflection_Types.term FStar_Pervasives_Native.option ->
      FStarC_Reflection_Types.term Prims.list ->
        (FStarC_Reflection_Types.term FStar_Pervasives_Native.option, 
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun e ->
    fun opt_t ->
      fun params -> opt_tapply (fun t -> mk_app_norm e t params) opt_t
let rec unzip :
  'a 'b . ('a * 'b) Prims.list -> ('a Prims.list * 'b Prims.list) =
  fun l ->
    match l with
    | [] -> ([], [])
    | (hd1, hd2)::tl ->
        let uu___ = unzip tl in
        (match uu___ with | (tl1, tl2) -> ((hd1 :: tl1), (hd2 :: tl2)))
let (abv_to_string :
  FStarC_Reflection_Types.bv ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun bv ->
    let uu___ =
      Obj.magic
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___1 -> FStarC_Reflection_V1_Builtins.inspect_bv bv)) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.InteractiveHelpers.Base.fst"
               (Prims.of_int (84)) (Prims.of_int (12)) (Prims.of_int (84))
               (Prims.of_int (25)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.InteractiveHelpers.Base.fst"
               (Prims.of_int (85)) (Prims.of_int (2)) (Prims.of_int (85))
               (Prims.of_int (60))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun bvv ->
            let uu___1 = FStar_Tactics_V1_Derived.name_of_bv bv in
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range
                          "FStar.InteractiveHelpers.Base.fst"
                          (Prims.of_int (85)) (Prims.of_int (2))
                          (Prims.of_int (85)) (Prims.of_int (15)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "Prims.fst" (Prims.of_int (611))
                          (Prims.of_int (19)) (Prims.of_int (611))
                          (Prims.of_int (31))))) (Obj.magic uu___1)
                 (fun uu___2 ->
                    FStar_Tactics_Effect.lift_div_tac
                      (fun uu___3 ->
                         Prims.strcat uu___2
                           (Prims.strcat " (%"
                              (Prims.strcat
                                 (Prims.string_of_int
                                    bvv.FStarC_Reflection_V1_Data.bv_index)
                                 ")")))))) uu___1)
let (print_binder_info :
  Prims.bool ->
    FStarC_Reflection_Types.binder ->
      (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun full ->
    fun b ->
      match FStarC_Reflection_V1_Builtins.inspect_binder b with
      | { FStarC_Reflection_V1_Data.binder_bv = binder_bv;
          FStarC_Reflection_V1_Data.binder_qual = binder_qual;
          FStarC_Reflection_V1_Data.binder_attrs = binder_attrs;
          FStarC_Reflection_V1_Data.binder_sort = binder_sort;_} ->
          let uu___ =
            match binder_qual with
            | FStarC_Reflection_V1_Data.Q_Implicit ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___1 -> "Implicit")))
            | FStarC_Reflection_V1_Data.Q_Explicit ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___1 -> "Explicit")))
            | FStarC_Reflection_V1_Data.Q_Meta t ->
                Obj.magic
                  (Obj.repr
                     (let uu___1 =
                        FStarC_Tactics_V1_Builtins.term_to_string t in
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.InteractiveHelpers.Base.fst"
                                 (Prims.of_int (92)) (Prims.of_int (29))
                                 (Prims.of_int (92)) (Prims.of_int (45)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "Prims.fst"
                                 (Prims.of_int (611)) (Prims.of_int (19))
                                 (Prims.of_int (611)) (Prims.of_int (31)))))
                        (Obj.magic uu___1)
                        (fun uu___2 ->
                           FStar_Tactics_Effect.lift_div_tac
                             (fun uu___3 -> Prims.strcat "Meta: " uu___2)))) in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.InteractiveHelpers.Base.fst"
                     (Prims.of_int (89)) (Prims.of_int (17))
                     (Prims.of_int (92)) (Prims.of_int (45)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.InteractiveHelpers.Base.fst"
                     (Prims.of_int (93)) (Prims.of_int (4))
                     (Prims.of_int (105)) (Prims.of_int (33)))))
            (Obj.magic uu___)
            (fun uu___1 ->
               (fun qual_str ->
                  let uu___1 =
                    Obj.magic
                      (FStar_Tactics_Effect.lift_div_tac
                         (fun uu___2 ->
                            FStarC_Reflection_V1_Builtins.inspect_bv
                              binder_bv)) in
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.InteractiveHelpers.Base.fst"
                                (Prims.of_int (94)) (Prims.of_int (14))
                                (Prims.of_int (94)) (Prims.of_int (34)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.InteractiveHelpers.Base.fst"
                                (Prims.of_int (95)) (Prims.of_int (2))
                                (Prims.of_int (105)) (Prims.of_int (33)))))
                       (Obj.magic uu___1)
                       (fun uu___2 ->
                          (fun bview ->
                             if full
                             then
                               let uu___2 =
                                 let uu___3 =
                                   let uu___4 =
                                     let uu___5 =
                                       FStar_Tactics_V1_Derived.name_of_binder
                                         b in
                                     FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.InteractiveHelpers.Base.fst"
                                                (Prims.of_int (98))
                                                (Prims.of_int (21))
                                                (Prims.of_int (98))
                                                (Prims.of_int (39)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.InteractiveHelpers.Base.fst"
                                                (Prims.of_int (98))
                                                (Prims.of_int (21))
                                                (Prims.of_int (103))
                                                (Prims.of_int (47)))))
                                       (Obj.magic uu___5)
                                       (fun uu___6 ->
                                          (fun uu___6 ->
                                             let uu___7 =
                                               let uu___8 =
                                                 let uu___9 =
                                                   FStar_Tactics_V1_Derived.binder_to_string
                                                     b in
                                                 FStar_Tactics_Effect.tac_bind
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "FStar.InteractiveHelpers.Base.fst"
                                                            (Prims.of_int (99))
                                                            (Prims.of_int (26))
                                                            (Prims.of_int (99))
                                                            (Prims.of_int (46)))))
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "FStar.InteractiveHelpers.Base.fst"
                                                            (Prims.of_int (99))
                                                            (Prims.of_int (26))
                                                            (Prims.of_int (103))
                                                            (Prims.of_int (47)))))
                                                   (Obj.magic uu___9)
                                                   (fun uu___10 ->
                                                      (fun uu___10 ->
                                                         let uu___11 =
                                                           let uu___12 =
                                                             let uu___13 =
                                                               let uu___14 =
                                                                 let uu___15
                                                                   =
                                                                   FStar_Tactics_V1_Derived.name_of_bv
                                                                    binder_bv in
                                                                 FStar_Tactics_Effect.tac_bind
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (101))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (101))
                                                                    (Prims.of_int (43)))))
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (101))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (103))
                                                                    (Prims.of_int (47)))))
                                                                   (Obj.magic
                                                                    uu___15)
                                                                   (fun
                                                                    uu___16
                                                                    ->
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    let uu___17
                                                                    =
                                                                    let uu___18
                                                                    =
                                                                    let uu___19
                                                                    =
                                                                    let uu___20
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.term_to_string
                                                                    binder_sort in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (103))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (103))
                                                                    (Prims.of_int (47)))))
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
                                                                    "\n- sort: "
                                                                    uu___21)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (103))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (103))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
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
                                                                    (Prims.string_of_int
                                                                    bview.FStarC_Reflection_V1_Data.bv_index)
                                                                    uu___20)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (102))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (103))
                                                                    (Prims.of_int (47)))))
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
                                                                    "\n- index: "
                                                                    uu___19)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (102))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (103))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___17)
                                                                    (fun
                                                                    uu___18
                                                                    ->
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
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (101))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (103))
                                                                    (Prims.of_int (47)))))
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
                                                                    uu___14)
                                                                 (fun uu___15
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    Prims.strcat
                                                                    "\n- ppname: "
                                                                    uu___15)) in
                                                             FStar_Tactics_Effect.tac_bind
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (101))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (103))
                                                                    (Prims.of_int (47)))))
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
                                                               (fun uu___14
                                                                  ->
                                                                  FStar_Tactics_Effect.lift_div_tac
                                                                    (
                                                                    fun
                                                                    uu___15
                                                                    ->
                                                                    Prims.strcat
                                                                    qual_str
                                                                    uu___14)) in
                                                           FStar_Tactics_Effect.tac_bind
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (100))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (103))
                                                                    (Prims.of_int (47)))))
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
                                                             (fun uu___13 ->
                                                                FStar_Tactics_Effect.lift_div_tac
                                                                  (fun
                                                                    uu___14
                                                                    ->
                                                                    Prims.strcat
                                                                    "\n- aqual: "
                                                                    uu___13)) in
                                                         Obj.magic
                                                           (FStar_Tactics_Effect.tac_bind
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (100))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (103))
                                                                    (Prims.of_int (47)))))
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                              (Obj.magic
                                                                 uu___11)
                                                              (fun uu___12 ->
                                                                 FStar_Tactics_Effect.lift_div_tac
                                                                   (fun
                                                                    uu___13
                                                                    ->
                                                                    Prims.strcat
                                                                    uu___10
                                                                    uu___12))))
                                                        uu___10) in
                                               FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "FStar.InteractiveHelpers.Base.fst"
                                                          (Prims.of_int (99))
                                                          (Prims.of_int (26))
                                                          (Prims.of_int (103))
                                                          (Prims.of_int (47)))))
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
                                                         Prims.strcat
                                                           "\n- as string: "
                                                           uu___9)) in
                                             Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.InteractiveHelpers.Base.fst"
                                                           (Prims.of_int (99))
                                                           (Prims.of_int (6))
                                                           (Prims.of_int (103))
                                                           (Prims.of_int (47)))))
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
                                                          Prims.strcat uu___6
                                                            uu___8)))) uu___6) in
                                   FStar_Tactics_Effect.tac_bind
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "FStar.InteractiveHelpers.Base.fst"
                                              (Prims.of_int (98))
                                              (Prims.of_int (21))
                                              (Prims.of_int (103))
                                              (Prims.of_int (47)))))
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
                                             Prims.strcat "\n- name: " uu___5)) in
                                 FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "FStar.InteractiveHelpers.Base.fst"
                                            (Prims.of_int (98))
                                            (Prims.of_int (6))
                                            (Prims.of_int (103))
                                            (Prims.of_int (47)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range "Prims.fst"
                                            (Prims.of_int (611))
                                            (Prims.of_int (19))
                                            (Prims.of_int (611))
                                            (Prims.of_int (31)))))
                                   (Obj.magic uu___3)
                                   (fun uu___4 ->
                                      FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___5 ->
                                           Prims.strcat
                                             "> print_binder_info:" uu___4)) in
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.InteractiveHelpers.Base.fst"
                                             (Prims.of_int (96))
                                             (Prims.of_int (10))
                                             (Prims.of_int (104))
                                             (Prims.of_int (5)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.InteractiveHelpers.Base.fst"
                                             (Prims.of_int (96))
                                             (Prims.of_int (4))
                                             (Prims.of_int (104))
                                             (Prims.of_int (5)))))
                                    (Obj.magic uu___2)
                                    (fun uu___3 ->
                                       (fun uu___3 ->
                                          Obj.magic
                                            (FStarC_Tactics_V1_Builtins.print
                                               uu___3)) uu___3))
                             else
                               (let uu___3 =
                                  FStar_Tactics_V1_Derived.binder_to_string b in
                                Obj.magic
                                  (FStar_Tactics_Effect.tac_bind
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "FStar.InteractiveHelpers.Base.fst"
                                              (Prims.of_int (105))
                                              (Prims.of_int (13))
                                              (Prims.of_int (105))
                                              (Prims.of_int (33)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "FStar.InteractiveHelpers.Base.fst"
                                              (Prims.of_int (105))
                                              (Prims.of_int (7))
                                              (Prims.of_int (105))
                                              (Prims.of_int (33)))))
                                     (Obj.magic uu___3)
                                     (fun uu___4 ->
                                        (fun uu___4 ->
                                           Obj.magic
                                             (FStarC_Tactics_V1_Builtins.print
                                                uu___4)) uu___4)))) uu___2)))
                 uu___1)
let (print_binders_info :
  Prims.bool ->
    FStarC_Reflection_Types.env -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun full ->
    fun e ->
      FStar_Tactics_Util.iter (print_binder_info full)
        (FStarC_Reflection_V1_Builtins.binders_of_env e)
let (acomp_to_string :
  FStarC_Reflection_Types.comp ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun c ->
    match FStarC_Reflection_V1_Builtins.inspect_comp c with
    | FStarC_Reflection_V1_Data.C_Total ret ->
        let uu___ =
          let uu___1 = FStarC_Tactics_V1_Builtins.term_to_string ret in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.InteractiveHelpers.Base.fst"
                     (Prims.of_int (113)) (Prims.of_int (18))
                     (Prims.of_int (113)) (Prims.of_int (36)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Prims.fst" (Prims.of_int (611))
                     (Prims.of_int (19)) (Prims.of_int (611))
                     (Prims.of_int (31))))) (Obj.magic uu___1)
            (fun uu___2 ->
               FStar_Tactics_Effect.lift_div_tac
                 (fun uu___3 -> Prims.strcat uu___2 ")")) in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.InteractiveHelpers.Base.fst"
                   (Prims.of_int (113)) (Prims.of_int (18))
                   (Prims.of_int (113)) (Prims.of_int (42)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Prims.fst" (Prims.of_int (611))
                   (Prims.of_int (19)) (Prims.of_int (611))
                   (Prims.of_int (31))))) (Obj.magic uu___)
          (fun uu___1 ->
             FStar_Tactics_Effect.lift_div_tac
               (fun uu___2 -> Prims.strcat "C_Total (" uu___1))
    | FStarC_Reflection_V1_Data.C_GTotal ret ->
        let uu___ =
          let uu___1 = FStarC_Tactics_V1_Builtins.term_to_string ret in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.InteractiveHelpers.Base.fst"
                     (Prims.of_int (115)) (Prims.of_int (19))
                     (Prims.of_int (115)) (Prims.of_int (37)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Prims.fst" (Prims.of_int (611))
                     (Prims.of_int (19)) (Prims.of_int (611))
                     (Prims.of_int (31))))) (Obj.magic uu___1)
            (fun uu___2 ->
               FStar_Tactics_Effect.lift_div_tac
                 (fun uu___3 -> Prims.strcat uu___2 ")")) in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.InteractiveHelpers.Base.fst"
                   (Prims.of_int (115)) (Prims.of_int (19))
                   (Prims.of_int (115)) (Prims.of_int (43)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Prims.fst" (Prims.of_int (611))
                   (Prims.of_int (19)) (Prims.of_int (611))
                   (Prims.of_int (31))))) (Obj.magic uu___)
          (fun uu___1 ->
             FStar_Tactics_Effect.lift_div_tac
               (fun uu___2 -> Prims.strcat "C_GTotal (" uu___1))
    | FStarC_Reflection_V1_Data.C_Lemma (pre, post, patterns) ->
        let uu___ =
          let uu___1 = FStarC_Tactics_V1_Builtins.term_to_string pre in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.InteractiveHelpers.Base.fst"
                     (Prims.of_int (117)) (Prims.of_int (18))
                     (Prims.of_int (117)) (Prims.of_int (36)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.InteractiveHelpers.Base.fst"
                     (Prims.of_int (117)) (Prims.of_int (18))
                     (Prims.of_int (117)) (Prims.of_int (72)))))
            (Obj.magic uu___1)
            (fun uu___2 ->
               (fun uu___2 ->
                  let uu___3 =
                    let uu___4 =
                      let uu___5 =
                        FStarC_Tactics_V1_Builtins.term_to_string post in
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.InteractiveHelpers.Base.fst"
                                 (Prims.of_int (117)) (Prims.of_int (47))
                                 (Prims.of_int (117)) (Prims.of_int (66)))))
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
                               "FStar.InteractiveHelpers.Base.fst"
                               (Prims.of_int (117)) (Prims.of_int (47))
                               (Prims.of_int (117)) (Prims.of_int (72)))))
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
                                "FStar.InteractiveHelpers.Base.fst"
                                (Prims.of_int (117)) (Prims.of_int (39))
                                (Prims.of_int (117)) (Prims.of_int (72)))))
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
                (FStar_Range.mk_range "FStar.InteractiveHelpers.Base.fst"
                   (Prims.of_int (117)) (Prims.of_int (18))
                   (Prims.of_int (117)) (Prims.of_int (72)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Prims.fst" (Prims.of_int (611))
                   (Prims.of_int (19)) (Prims.of_int (611))
                   (Prims.of_int (31))))) (Obj.magic uu___)
          (fun uu___1 ->
             FStar_Tactics_Effect.lift_div_tac
               (fun uu___2 -> Prims.strcat "C_Lemma (" uu___1))
    | FStarC_Reflection_V1_Data.C_Eff (us, eff_name, result, eff_args, uu___)
        ->
        let uu___1 =
          Obj.magic
            (FStar_Tactics_Effect.lift_div_tac
               (fun uu___2 ->
                  fun a ->
                    let uu___3 =
                      let uu___4 =
                        FStarC_Tactics_V1_Builtins.term_to_string a in
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.InteractiveHelpers.Base.fst"
                                 (Prims.of_int (120)) (Prims.of_int (13))
                                 (Prims.of_int (120)) (Prims.of_int (29)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "Prims.fst"
                                 (Prims.of_int (611)) (Prims.of_int (19))
                                 (Prims.of_int (611)) (Prims.of_int (31)))))
                        (Obj.magic uu___4)
                        (fun uu___5 ->
                           FStar_Tactics_Effect.lift_div_tac
                             (fun uu___6 -> Prims.strcat uu___5 ")")) in
                    FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range
                               "FStar.InteractiveHelpers.Base.fst"
                               (Prims.of_int (120)) (Prims.of_int (13))
                               (Prims.of_int (120)) (Prims.of_int (35)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Prims.fst"
                               (Prims.of_int (611)) (Prims.of_int (19))
                               (Prims.of_int (611)) (Prims.of_int (31)))))
                      (Obj.magic uu___3)
                      (fun uu___4 ->
                         FStar_Tactics_Effect.lift_div_tac
                           (fun uu___5 -> Prims.strcat " (" uu___4)))) in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.InteractiveHelpers.Base.fst"
                   (Prims.of_int (120)) (Prims.of_int (6))
                   (Prims.of_int (120)) (Prims.of_int (35)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.InteractiveHelpers.Base.fst"
                   (Prims.of_int (121)) (Prims.of_int (6))
                   (Prims.of_int (124)) (Prims.of_int (86)))))
          (Obj.magic uu___1)
          (fun uu___2 ->
             (fun eff_arg_to_string ->
                let uu___2 =
                  FStar_Tactics_Util.map
                    (fun uu___3 ->
                       match uu___3 with | (x, y) -> eff_arg_to_string x)
                    eff_args in
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.InteractiveHelpers.Base.fst"
                              (Prims.of_int (122)) (Prims.of_int (19))
                              (Prims.of_int (122)) (Prims.of_int (67)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.InteractiveHelpers.Base.fst"
                              (Prims.of_int (122)) (Prims.of_int (70))
                              (Prims.of_int (124)) (Prims.of_int (86)))))
                     (Obj.magic uu___2)
                     (fun uu___3 ->
                        (fun args_str ->
                           let uu___3 =
                             Obj.magic
                               (FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___4 ->
                                     FStar_List_Tot_Base.fold_left
                                       (fun x -> fun y -> Prims.strcat x y)
                                       "" args_str)) in
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.InteractiveHelpers.Base.fst"
                                         (Prims.of_int (123))
                                         (Prims.of_int (19))
                                         (Prims.of_int (123))
                                         (Prims.of_int (68)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.InteractiveHelpers.Base.fst"
                                         (Prims.of_int (124))
                                         (Prims.of_int (4))
                                         (Prims.of_int (124))
                                         (Prims.of_int (86)))))
                                (Obj.magic uu___3)
                                (fun uu___4 ->
                                   (fun args_str1 ->
                                      let uu___4 =
                                        let uu___5 =
                                          let uu___6 =
                                            let uu___7 =
                                              FStarC_Tactics_V1_Builtins.term_to_string
                                                result in
                                            FStar_Tactics_Effect.tac_bind
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "FStar.InteractiveHelpers.Base.fst"
                                                       (Prims.of_int (124))
                                                       (Prims.of_int (48))
                                                       (Prims.of_int (124))
                                                       (Prims.of_int (69)))))
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
                                                        (Prims.strcat ")"
                                                           args_str1))) in
                                          FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "FStar.InteractiveHelpers.Base.fst"
                                                     (Prims.of_int (124))
                                                     (Prims.of_int (48))
                                                     (Prims.of_int (124))
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
                                                    Prims.strcat ") (" uu___7)) in
                                        FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "FStar.InteractiveHelpers.Base.fst"
                                                   (Prims.of_int (124))
                                                   (Prims.of_int (40))
                                                   (Prims.of_int (124))
                                                   (Prims.of_int (86)))))
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
                                                    (FStar_Reflection_V1_Derived.flatten_name
                                                       eff_name) uu___6)) in
                                      Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "FStar.InteractiveHelpers.Base.fst"
                                                    (Prims.of_int (124))
                                                    (Prims.of_int (16))
                                                    (Prims.of_int (124))
                                                    (Prims.of_int (86)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Prims.fst"
                                                    (Prims.of_int (611))
                                                    (Prims.of_int (19))
                                                    (Prims.of_int (611))
                                                    (Prims.of_int (31)))))
                                           (Obj.magic uu___4)
                                           (fun uu___5 ->
                                              FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___6 ->
                                                   Prims.strcat "C_Eff ("
                                                     uu___5)))) uu___4)))
                          uu___3))) uu___2)
exception MetaAnalysis of FStarC_Errors_Msg.error_message 
let (uu___is_MetaAnalysis : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | MetaAnalysis uu___ -> true | uu___ -> false
let (__proj__MetaAnalysis__item__uu___ :
  Prims.exn -> FStarC_Errors_Msg.error_message) =
  fun projectee -> match projectee with | MetaAnalysis uu___ -> uu___
let mfail_doc :
  'uuuuu .
    FStarC_Errors_Msg.error_message ->
      ('uuuuu, unit) FStar_Tactics_Effect.tac_repr
  =
  fun uu___ ->
    (fun m -> Obj.magic (FStar_Tactics_Effect.raise (MetaAnalysis m))) uu___
let mfail :
  'uuuuu . Prims.string -> ('uuuuu, unit) FStar_Tactics_Effect.tac_repr =
  fun uu___ ->
    (fun str ->
       Obj.magic
         (FStar_Tactics_Effect.raise
            (MetaAnalysis (FStarC_Errors_Msg.mkmsg str)))) uu___
let (print_dbg :
  Prims.bool -> Prims.string -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___1 ->
    fun uu___ ->
      (fun debug ->
         fun s ->
           if debug
           then Obj.magic (Obj.repr (FStarC_Tactics_V1_Builtins.print s))
           else
             Obj.magic
               (Obj.repr
                  (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> ()))))
        uu___1 uu___
let (term_view_construct :
  FStarC_Reflection_V1_Data.term_view ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    (fun t ->
       Obj.magic
         (FStar_Tactics_Effect.lift_div_tac
            (fun uu___ ->
               match t with
               | FStarC_Reflection_V1_Data.Tv_Var uu___1 -> "Tv_Var"
               | FStarC_Reflection_V1_Data.Tv_BVar uu___1 -> "Tv_BVar"
               | FStarC_Reflection_V1_Data.Tv_FVar uu___1 -> "Tv_FVar"
               | FStarC_Reflection_V1_Data.Tv_App (uu___1, uu___2) ->
                   "Tv_App"
               | FStarC_Reflection_V1_Data.Tv_Abs (uu___1, uu___2) ->
                   "Tv_Abs"
               | FStarC_Reflection_V1_Data.Tv_Arrow (uu___1, uu___2) ->
                   "Tv_Arrow"
               | FStarC_Reflection_V1_Data.Tv_Type uu___1 -> "Tv_Type"
               | FStarC_Reflection_V1_Data.Tv_Refine (uu___1, uu___2, uu___3)
                   -> "Tv_Refine"
               | FStarC_Reflection_V1_Data.Tv_Const uu___1 -> "Tv_Const"
               | FStarC_Reflection_V1_Data.Tv_Uvar (uu___1, uu___2) ->
                   "Tv_Uvar"
               | FStarC_Reflection_V1_Data.Tv_Let
                   (uu___1, uu___2, uu___3, uu___4, uu___5, uu___6) ->
                   "Tv_Let"
               | FStarC_Reflection_V1_Data.Tv_Match (uu___1, uu___2, uu___3)
                   -> "Tv_Match"
               | FStarC_Reflection_V1_Data.Tv_AscribedT
                   (uu___1, uu___2, uu___3, uu___4) -> "Tv_AscribedT"
               | FStarC_Reflection_V1_Data.Tv_AscribedC
                   (uu___1, uu___2, uu___3, uu___4) -> "Tv_AScribedC"
               | uu___1 -> "Tv_Unknown"))) uu___
let (term_construct :
  FStarC_Reflection_Types.term ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    let uu___ = FStarC_Tactics_V1_Builtins.inspect t in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.InteractiveHelpers.Base.fst"
               (Prims.of_int (162)) (Prims.of_int (22)) (Prims.of_int (162))
               (Prims.of_int (33)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.InteractiveHelpers.Base.fst"
               (Prims.of_int (162)) (Prims.of_int (2)) (Prims.of_int (162))
               (Prims.of_int (33))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun uu___1 -> Obj.magic (term_view_construct uu___1)) uu___1)
let (filter_ascriptions :
  Prims.bool ->
    FStarC_Reflection_Types.term ->
      (FStarC_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun dbg ->
    fun t ->
      let uu___ =
        let uu___1 =
          let uu___2 =
            let uu___3 =
              let uu___4 = FStarC_Tactics_V1_Builtins.inspect t in
              FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range
                         "FStar.InteractiveHelpers.Base.fst"
                         (Prims.of_int (174)) (Prims.of_int (27))
                         (Prims.of_int (174)) (Prims.of_int (28)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range
                         "FStar.InteractiveHelpers.Base.fst"
                         (Prims.of_int (175)) (Prims.of_int (45))
                         (Prims.of_int (175)) (Prims.of_int (66)))))
                (Obj.magic uu___4)
                (fun uu___5 ->
                   (fun uu___5 -> Obj.magic (term_view_construct uu___5))
                     uu___5) in
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "FStar.InteractiveHelpers.Base.fst"
                       (Prims.of_int (175)) (Prims.of_int (45))
                       (Prims.of_int (175)) (Prims.of_int (66)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "FStar.InteractiveHelpers.Base.fst"
                       (Prims.of_int (175)) (Prims.of_int (45))
                       (Prims.of_int (175)) (Prims.of_int (92)))))
              (Obj.magic uu___3)
              (fun uu___4 ->
                 (fun uu___4 ->
                    let uu___5 =
                      let uu___6 =
                        FStarC_Tactics_V1_Builtins.term_to_string t in
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.InteractiveHelpers.Base.fst"
                                 (Prims.of_int (175)) (Prims.of_int (76))
                                 (Prims.of_int (175)) (Prims.of_int (92)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "Prims.fst"
                                 (Prims.of_int (611)) (Prims.of_int (19))
                                 (Prims.of_int (611)) (Prims.of_int (31)))))
                        (Obj.magic uu___6)
                        (fun uu___7 ->
                           FStar_Tactics_Effect.lift_div_tac
                             (fun uu___8 -> Prims.strcat ": " uu___7)) in
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.InteractiveHelpers.Base.fst"
                                  (Prims.of_int (175)) (Prims.of_int (69))
                                  (Prims.of_int (175)) (Prims.of_int (92)))))
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
                  (FStar_Range.mk_range "FStar.InteractiveHelpers.Base.fst"
                     (Prims.of_int (175)) (Prims.of_int (45))
                     (Prims.of_int (175)) (Prims.of_int (92)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Prims.fst" (Prims.of_int (611))
                     (Prims.of_int (19)) (Prims.of_int (611))
                     (Prims.of_int (31))))) (Obj.magic uu___2)
            (fun uu___3 ->
               FStar_Tactics_Effect.lift_div_tac
                 (fun uu___4 -> Prims.strcat "[> filter_ascriptions: " uu___3)) in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.InteractiveHelpers.Base.fst"
                   (Prims.of_int (175)) (Prims.of_int (16))
                   (Prims.of_int (175)) (Prims.of_int (94)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.InteractiveHelpers.Base.fst"
                   (Prims.of_int (175)) (Prims.of_int (2))
                   (Prims.of_int (175)) (Prims.of_int (94)))))
          (Obj.magic uu___1)
          (fun uu___2 ->
             (fun uu___2 -> Obj.magic (print_dbg dbg uu___2)) uu___2) in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.InteractiveHelpers.Base.fst"
                 (Prims.of_int (175)) (Prims.of_int (2)) (Prims.of_int (175))
                 (Prims.of_int (94)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.InteractiveHelpers.Base.fst"
                 (Prims.of_int (176)) (Prims.of_int (2)) (Prims.of_int (180))
                 (Prims.of_int (15))))) (Obj.magic uu___)
        (fun uu___1 ->
           (fun uu___1 ->
              Obj.magic
                (FStar_Tactics_Visit.visit_tm
                   (fun t1 ->
                      let uu___2 = FStarC_Tactics_V1_Builtins.inspect t1 in
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.InteractiveHelpers.Base.fst"
                                 (Prims.of_int (177)) (Prims.of_int (10))
                                 (Prims.of_int (177)) (Prims.of_int (19)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.InteractiveHelpers.Base.fst"
                                 (Prims.of_int (177)) (Prims.of_int (4))
                                 (Prims.of_int (180)) (Prims.of_int (12)))))
                        (Obj.magic uu___2)
                        (fun uu___3 ->
                           FStar_Tactics_Effect.lift_div_tac
                             (fun uu___4 ->
                                match uu___3 with
                                | FStarC_Reflection_V1_Data.Tv_AscribedT
                                    (e, uu___5, uu___6, uu___7) -> e
                                | FStarC_Reflection_V1_Data.Tv_AscribedC
                                    (e, uu___5, uu___6, uu___7) -> e
                                | uu___5 -> t1))) t)) uu___1)
let (prettify_term :
  Prims.bool ->
    FStarC_Reflection_Types.term ->
      (FStarC_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
  = fun dbg -> fun t -> filter_ascriptions dbg t
type 'a bind_map = (FStarC_Reflection_Types.bv * 'a) Prims.list
let bind_map_push :
  'a .
    'a bind_map ->
      FStarC_Reflection_Types.bv ->
        'a -> (FStarC_Reflection_Types.bv * 'a) Prims.list
  = fun m -> fun b -> fun x -> (b, x) :: m
let rec bind_map_get :
  'a .
    'a bind_map ->
      FStarC_Reflection_Types.bv -> 'a FStar_Pervasives_Native.option
  =
  fun m ->
    fun b ->
      match m with
      | [] -> FStar_Pervasives_Native.None
      | (b', x)::m' ->
          if (FStarC_Reflection_V1_Builtins.compare_bv b b') = FStar_Order.Eq
          then FStar_Pervasives_Native.Some x
          else bind_map_get m' b
let rec bind_map_get_from_name :
  'a .
    'a bind_map ->
      Prims.string ->
        ((FStarC_Reflection_Types.bv * 'a) FStar_Pervasives_Native.option,
          unit) FStar_Tactics_Effect.tac_repr
  =
  fun uu___1 ->
    fun uu___ ->
      (fun m ->
         fun name ->
           match m with
           | [] ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac
                       (fun uu___ -> FStar_Pervasives_Native.None)))
           | (b', x)::m' ->
               Obj.magic
                 (Obj.repr
                    (let uu___ =
                       Obj.magic
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___1 ->
                               FStarC_Reflection_V1_Builtins.inspect_bv b')) in
                     FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.InteractiveHelpers.Base.fst"
                                (Prims.of_int (211)) (Prims.of_int (14))
                                (Prims.of_int (211)) (Prims.of_int (27)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.InteractiveHelpers.Base.fst"
                                (Prims.of_int (212)) (Prims.of_int (4))
                                (Prims.of_int (212)) (Prims.of_int (88)))))
                       (Obj.magic uu___)
                       (fun uu___1 ->
                          (fun b'v ->
                             let uu___1 =
                               let uu___2 =
                                 FStarC_Tactics_Unseal.unseal
                                   b'v.FStarC_Reflection_V1_Data.bv_ppname in
                               FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "FStar.InteractiveHelpers.Base.fst"
                                          (Prims.of_int (212))
                                          (Prims.of_int (7))
                                          (Prims.of_int (212))
                                          (Prims.of_int (27)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "FStar.InteractiveHelpers.Base.fst"
                                          (Prims.of_int (212))
                                          (Prims.of_int (7))
                                          (Prims.of_int (212))
                                          (Prims.of_int (34)))))
                                 (Obj.magic uu___2)
                                 (fun uu___3 ->
                                    FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___4 -> uu___3 = name)) in
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "FStar.InteractiveHelpers.Base.fst"
                                           (Prims.of_int (212))
                                           (Prims.of_int (7))
                                           (Prims.of_int (212))
                                           (Prims.of_int (34)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "FStar.InteractiveHelpers.Base.fst"
                                           (Prims.of_int (212))
                                           (Prims.of_int (4))
                                           (Prims.of_int (212))
                                           (Prims.of_int (88)))))
                                  (Obj.magic uu___1)
                                  (fun uu___2 ->
                                     (fun uu___2 ->
                                        if uu___2
                                        then
                                          Obj.magic
                                            (Obj.repr
                                               (FStar_Tactics_Effect.lift_div_tac
                                                  (fun uu___3 ->
                                                     FStar_Pervasives_Native.Some
                                                       (b', x))))
                                        else
                                          Obj.magic
                                            (Obj.repr
                                               (bind_map_get_from_name m'
                                                  name))) uu___2))) uu___1))))
        uu___1 uu___
type genv =
  {
  env: FStarC_Reflection_Types.env ;
  bmap:
    (FStarC_Reflection_Types.typ * Prims.bool * FStarC_Reflection_Types.term)
      bind_map
    ;
  svars:
    (FStarC_Reflection_Types.bv * FStarC_Reflection_Types.typ) Prims.list }
let (__proj__Mkgenv__item__env : genv -> FStarC_Reflection_Types.env) =
  fun projectee -> match projectee with | { env; bmap; svars;_} -> env
let (__proj__Mkgenv__item__bmap :
  genv ->
    (FStarC_Reflection_Types.typ * Prims.bool * FStarC_Reflection_Types.term)
      bind_map)
  = fun projectee -> match projectee with | { env; bmap; svars;_} -> bmap
let (__proj__Mkgenv__item__svars :
  genv ->
    (FStarC_Reflection_Types.bv * FStarC_Reflection_Types.typ) Prims.list)
  = fun projectee -> match projectee with | { env; bmap; svars;_} -> svars
let (get_env : genv -> FStarC_Reflection_Types.env) = fun e -> e.env
let (get_bind_map :
  genv ->
    (FStarC_Reflection_Types.typ * Prims.bool * FStarC_Reflection_Types.term)
      bind_map)
  = fun e -> e.bmap
let (mk_genv :
  FStarC_Reflection_Types.env ->
    (FStarC_Reflection_Types.typ * Prims.bool * FStarC_Reflection_Types.term)
      bind_map ->
      (FStarC_Reflection_Types.bv * FStarC_Reflection_Types.typ) Prims.list
        -> genv)
  = fun env -> fun bmap -> fun svars -> { env; bmap; svars }
let (mk_init_genv : FStarC_Reflection_Types.env -> genv) =
  fun env -> mk_genv env [] []
let (genv_to_string :
  genv -> (Prims.string, unit) FStar_Tactics_Effect.tac_repr) =
  fun ge ->
    let uu___ =
      Obj.magic
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___1 ->
              fun b ->
                let uu___2 =
                  abv_to_string (FStar_Reflection_V1_Derived.bv_of_binder b) in
                FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range
                           "FStar.InteractiveHelpers.Base.fst"
                           (Prims.of_int (248)) (Prims.of_int (4))
                           (Prims.of_int (248)) (Prims.of_int (34)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Prims.fst"
                           (Prims.of_int (611)) (Prims.of_int (19))
                           (Prims.of_int (611)) (Prims.of_int (31)))))
                  (Obj.magic uu___2)
                  (fun uu___3 ->
                     FStar_Tactics_Effect.lift_div_tac
                       (fun uu___4 -> Prims.strcat uu___3 "\n")))) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.InteractiveHelpers.Base.fst"
               (Prims.of_int (248)) (Prims.of_int (4)) (Prims.of_int (248))
               (Prims.of_int (41)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.InteractiveHelpers.Base.fst"
               (Prims.of_int (249)) (Prims.of_int (4)) (Prims.of_int (261))
               (Prims.of_int (34))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun binder_to_string ->
            let uu___1 =
              FStar_Tactics_Util.map binder_to_string
                (FStarC_Reflection_V1_Builtins.binders_of_env ge.env) in
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range
                          "FStar.InteractiveHelpers.Base.fst"
                          (Prims.of_int (250)) (Prims.of_int (20))
                          (Prims.of_int (250)) (Prims.of_int (64)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range
                          "FStar.InteractiveHelpers.Base.fst"
                          (Prims.of_int (250)) (Prims.of_int (67))
                          (Prims.of_int (261)) (Prims.of_int (34)))))
                 (Obj.magic uu___1)
                 (fun uu___2 ->
                    (fun binders_str ->
                       let uu___2 =
                         Obj.magic
                           (FStar_Tactics_Effect.lift_div_tac
                              (fun uu___3 ->
                                 fun e ->
                                   let uu___4 =
                                     Obj.magic
                                       (FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___5 -> e)) in
                                   FStar_Tactics_Effect.tac_bind
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "FStar.InteractiveHelpers.Base.fst"
                                              (Prims.of_int (252))
                                              (Prims.of_int (30))
                                              (Prims.of_int (252))
                                              (Prims.of_int (31)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "FStar.InteractiveHelpers.Base.fst"
                                              (Prims.of_int (251))
                                              (Prims.of_int (71))
                                              (Prims.of_int (254))
                                              (Prims.of_int (57)))))
                                     (Obj.magic uu___4)
                                     (fun uu___5 ->
                                        (fun uu___5 ->
                                           match uu___5 with
                                           | (bv, (_sort, abs, t)) ->
                                               let uu___6 =
                                                 let uu___7 =
                                                   abv_to_string bv in
                                                 FStar_Tactics_Effect.tac_bind
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "FStar.InteractiveHelpers.Base.fst"
                                                            (Prims.of_int (253))
                                                            (Prims.of_int (10))
                                                            (Prims.of_int (253))
                                                            (Prims.of_int (26)))))
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "FStar.InteractiveHelpers.Base.fst"
                                                            (Prims.of_int (253))
                                                            (Prims.of_int (10))
                                                            (Prims.of_int (254))
                                                            (Prims.of_int (57)))))
                                                   (Obj.magic uu___7)
                                                   (fun uu___8 ->
                                                      (fun uu___8 ->
                                                         let uu___9 =
                                                           let uu___10 =
                                                             let uu___11 =
                                                               let uu___12 =
                                                                 let uu___13
                                                                   =
                                                                   FStarC_Tactics_V1_Builtins.term_to_string
                                                                    t in
                                                                 FStar_Tactics_Effect.tac_bind
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (254))
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (254))
                                                                    (Prims.of_int (48)))))
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
                                                                    uu___14
                                                                    "))\n")) in
                                                               FStar_Tactics_Effect.tac_bind
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (254))
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (254))
                                                                    (Prims.of_int (57)))))
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
                                                                    uu___12)
                                                                 (fun uu___13
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    Prims.strcat
                                                                    ", "
                                                                    uu___13)) in
                                                             FStar_Tactics_Effect.tac_bind
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (254))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (254))
                                                                    (Prims.of_int (57)))))
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                               (Obj.magic
                                                                  uu___11)
                                                               (fun uu___12
                                                                  ->
                                                                  FStar_Tactics_Effect.lift_div_tac
                                                                    (
                                                                    fun
                                                                    uu___13
                                                                    ->
                                                                    Prims.strcat
                                                                    (Prims.string_of_bool
                                                                    abs)
                                                                    uu___12)) in
                                                           FStar_Tactics_Effect.tac_bind
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (254))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (254))
                                                                    (Prims.of_int (57)))))
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                             (Obj.magic
                                                                uu___10)
                                                             (fun uu___11 ->
                                                                FStar_Tactics_Effect.lift_div_tac
                                                                  (fun
                                                                    uu___12
                                                                    ->
                                                                    Prims.strcat
                                                                    " -> ("
                                                                    uu___11)) in
                                                         Obj.magic
                                                           (FStar_Tactics_Effect.tac_bind
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (253))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (254))
                                                                    (Prims.of_int (57)))))
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                              (Obj.magic
                                                                 uu___9)
                                                              (fun uu___10 ->
                                                                 FStar_Tactics_Effect.lift_div_tac
                                                                   (fun
                                                                    uu___11
                                                                    ->
                                                                    Prims.strcat
                                                                    uu___8
                                                                    uu___10))))
                                                        uu___8) in
                                               Obj.magic
                                                 (FStar_Tactics_Effect.tac_bind
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "FStar.InteractiveHelpers.Base.fst"
                                                             (Prims.of_int (253))
                                                             (Prims.of_int (10))
                                                             (Prims.of_int (254))
                                                             (Prims.of_int (57)))))
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
                                                            Prims.strcat "("
                                                              uu___7))))
                                          uu___5))) in
                       Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.InteractiveHelpers.Base.fst"
                                     (Prims.of_int (251)) (Prims.of_int (71))
                                     (Prims.of_int (254)) (Prims.of_int (57)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.InteractiveHelpers.Base.fst"
                                     (Prims.of_int (255)) (Prims.of_int (4))
                                     (Prims.of_int (261)) (Prims.of_int (34)))))
                            (Obj.magic uu___2)
                            (fun uu___3 ->
                               (fun bmap_elem_to_string ->
                                  let uu___3 =
                                    FStar_Tactics_Util.map
                                      bmap_elem_to_string ge.bmap in
                                  Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.InteractiveHelpers.Base.fst"
                                                (Prims.of_int (256))
                                                (Prims.of_int (17))
                                                (Prims.of_int (256))
                                                (Prims.of_int (48)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.InteractiveHelpers.Base.fst"
                                                (Prims.of_int (256))
                                                (Prims.of_int (51))
                                                (Prims.of_int (261))
                                                (Prims.of_int (34)))))
                                       (Obj.magic uu___3)
                                       (fun uu___4 ->
                                          (fun bmap_str ->
                                             let uu___4 =
                                               FStar_Tactics_Util.map
                                                 (fun uu___5 ->
                                                    match uu___5 with
                                                    | (bv, uu___6) ->
                                                        let uu___7 =
                                                          abv_to_string bv in
                                                        FStar_Tactics_Effect.tac_bind
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "FStar.InteractiveHelpers.Base.fst"
                                                                   (Prims.of_int (257))
                                                                   (Prims.of_int (38))
                                                                   (Prims.of_int (257))
                                                                   (Prims.of_int (54)))))
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
                                                                  Prims.strcat
                                                                    uu___8
                                                                    "\n")))
                                                 ge.svars in
                                             Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.InteractiveHelpers.Base.fst"
                                                           (Prims.of_int (257))
                                                           (Prims.of_int (18))
                                                           (Prims.of_int (257))
                                                           (Prims.of_int (71)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Prims.fst"
                                                           (Prims.of_int (611))
                                                           (Prims.of_int (19))
                                                           (Prims.of_int (611))
                                                           (Prims.of_int (31)))))
                                                  (Obj.magic uu___4)
                                                  (fun svars_str ->
                                                     FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___5 ->
                                                          Prims.strcat
                                                            "> env:\n"
                                                            (Prims.strcat
                                                               (FStar_List_Tot_Base.fold_left
                                                                  (fun x ->
                                                                    fun y ->
                                                                    Prims.strcat
                                                                    x y) ""
                                                                  binders_str)
                                                               (Prims.strcat
                                                                  "> bmap:\n"
                                                                  (Prims.strcat
                                                                    (FStar_List_Tot_Base.fold_left
                                                                    (fun x ->
                                                                    fun y ->
                                                                    Prims.strcat
                                                                    x y) ""
                                                                    bmap_str)
                                                                    (Prims.strcat
                                                                    "> svars:\n"
                                                                    (FStar_List_Tot_Base.fold_left
                                                                    (fun x ->
                                                                    fun y ->
                                                                    Prims.strcat
                                                                    x y) ""
                                                                    svars_str)))))))))
                                            uu___4))) uu___3))) uu___2)))
           uu___1)
let (genv_get :
  genv ->
    FStarC_Reflection_Types.bv ->
      (FStarC_Reflection_Types.typ * Prims.bool *
        FStarC_Reflection_Types.term) FStar_Pervasives_Native.option)
  = fun ge -> fun b -> bind_map_get ge.bmap b
let (genv_get_from_name :
  genv ->
    Prims.string ->
      (((FStarC_Reflection_Types.bv * FStarC_Reflection_Types.typ) *
         (Prims.bool * FStarC_Reflection_Types.term))
         FStar_Pervasives_Native.option,
        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun ge ->
    fun name ->
      let uu___ = bind_map_get_from_name ge.bmap name in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.InteractiveHelpers.Base.fst"
                 (Prims.of_int (268)) (Prims.of_int (8)) (Prims.of_int (268))
                 (Prims.of_int (43)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.InteractiveHelpers.Base.fst"
                 (Prims.of_int (268)) (Prims.of_int (2)) (Prims.of_int (270))
                 (Prims.of_int (56))))) (Obj.magic uu___)
        (fun uu___1 ->
           FStar_Tactics_Effect.lift_div_tac
             (fun uu___2 ->
                match uu___1 with
                | FStar_Pervasives_Native.None ->
                    FStar_Pervasives_Native.None
                | FStar_Pervasives_Native.Some (bv, (sort, b, x)) ->
                    FStar_Pervasives_Native.Some ((bv, sort), (b, x))))
let (genv_push_bv :
  genv ->
    FStarC_Reflection_Types.bv ->
      FStarC_Reflection_Types.typ ->
        Prims.bool ->
          FStarC_Reflection_Types.term FStar_Pervasives_Native.option ->
            (genv, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun ge ->
    fun b ->
      fun sort ->
        fun abs ->
          fun t ->
            let uu___ =
              Obj.magic
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___1 ->
                      FStar_Reflection_V1_Derived.mk_binder b sort)) in
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "FStar.InteractiveHelpers.Base.fst"
                       (Prims.of_int (275)) (Prims.of_int (11))
                       (Prims.of_int (275)) (Prims.of_int (27)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "FStar.InteractiveHelpers.Base.fst"
                       (Prims.of_int (275)) (Prims.of_int (30))
                       (Prims.of_int (281)) (Prims.of_int (25)))))
              (Obj.magic uu___)
              (fun uu___1 ->
                 (fun br ->
                    let uu___1 =
                      let uu___2 = FStar_Tactics_V1_Derived.name_of_bv b in
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.InteractiveHelpers.Base.fst"
                                 (Prims.of_int (276)) (Prims.of_int (33))
                                 (Prims.of_int (276)) (Prims.of_int (47)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.InteractiveHelpers.Base.fst"
                                 (Prims.of_int (276)) (Prims.of_int (11))
                                 (Prims.of_int (276)) (Prims.of_int (47)))))
                        (Obj.magic uu___2)
                        (fun uu___3 ->
                           (fun uu___3 ->
                              Obj.magic (genv_get_from_name ge uu___3))
                             uu___3) in
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.InteractiveHelpers.Base.fst"
                                  (Prims.of_int (276)) (Prims.of_int (11))
                                  (Prims.of_int (276)) (Prims.of_int (47)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.InteractiveHelpers.Base.fst"
                                  (Prims.of_int (276)) (Prims.of_int (50))
                                  (Prims.of_int (281)) (Prims.of_int (25)))))
                         (Obj.magic uu___1)
                         (fun uu___2 ->
                            (fun sv ->
                               let uu___2 =
                                 Obj.magic
                                   (FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___3 ->
                                         if
                                           FStar_Pervasives_Native.uu___is_Some
                                             sv
                                         then
                                           (FStar_Pervasives_Native.fst
                                              (FStar_Pervasives_Native.__proj__Some__item__v
                                                 sv))
                                           :: (ge.svars)
                                         else ge.svars)) in
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.InteractiveHelpers.Base.fst"
                                             (Prims.of_int (277))
                                             (Prims.of_int (15))
                                             (Prims.of_int (277))
                                             (Prims.of_int (74)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.InteractiveHelpers.Base.fst"
                                             (Prims.of_int (277))
                                             (Prims.of_int (77))
                                             (Prims.of_int (281))
                                             (Prims.of_int (25)))))
                                    (Obj.magic uu___2)
                                    (fun uu___3 ->
                                       (fun svars' ->
                                          let uu___3 =
                                            Obj.magic
                                              (FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___4 ->
                                                    FStarC_Reflection_V1_Builtins.push_binder
                                                      ge.env br)) in
                                          Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "FStar.InteractiveHelpers.Base.fst"
                                                        (Prims.of_int (278))
                                                        (Prims.of_int (11))
                                                        (Prims.of_int (278))
                                                        (Prims.of_int (32)))))
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "FStar.InteractiveHelpers.Base.fst"
                                                        (Prims.of_int (278))
                                                        (Prims.of_int (35))
                                                        (Prims.of_int (281))
                                                        (Prims.of_int (25)))))
                                               (Obj.magic uu___3)
                                               (fun uu___4 ->
                                                  (fun e' ->
                                                     let uu___4 =
                                                       if
                                                         FStar_Pervasives_Native.uu___is_Some
                                                           t
                                                       then
                                                         Obj.magic
                                                           (Obj.repr
                                                              (FStar_Tactics_Effect.lift_div_tac
                                                                 (fun uu___5
                                                                    ->
                                                                    FStar_Pervasives_Native.__proj__Some__item__v
                                                                    t)))
                                                       else
                                                         Obj.magic
                                                           (Obj.repr
                                                              (FStarC_Tactics_V1_Builtins.pack
                                                                 (FStarC_Reflection_V1_Data.Tv_Var
                                                                    b))) in
                                                     Obj.magic
                                                       (FStar_Tactics_Effect.tac_bind
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "FStar.InteractiveHelpers.Base.fst"
                                                                   (Prims.of_int (279))
                                                                   (Prims.of_int (11))
                                                                   (Prims.of_int (279))
                                                                   (Prims.of_int (57)))))
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "FStar.InteractiveHelpers.Base.fst"
                                                                   (Prims.of_int (281))
                                                                   (Prims.of_int (2))
                                                                   (Prims.of_int (281))
                                                                   (Prims.of_int (25)))))
                                                          (Obj.magic uu___4)
                                                          (fun tm ->
                                                             FStar_Tactics_Effect.lift_div_tac
                                                               (fun uu___5 ->
                                                                  mk_genv e'
                                                                    (
                                                                    bind_map_push
                                                                    ge.bmap b
                                                                    (sort,
                                                                    abs, tm))
                                                                    svars'))))
                                                    uu___4))) uu___3)))
                              uu___2))) uu___1)
let (genv_push_binder :
  genv ->
    FStarC_Reflection_Types.binder ->
      Prims.bool ->
        FStarC_Reflection_Types.term FStar_Pervasives_Native.option ->
          (genv, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun ge ->
    fun b ->
      fun abs ->
        fun t ->
          let uu___ = FStar_Tactics_V1_Derived.binder_sort b in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.InteractiveHelpers.Base.fst"
                     (Prims.of_int (284)) (Prims.of_int (35))
                     (Prims.of_int (284)) (Prims.of_int (50)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.InteractiveHelpers.Base.fst"
                     (Prims.of_int (284)) (Prims.of_int (2))
                     (Prims.of_int (284)) (Prims.of_int (56)))))
            (Obj.magic uu___)
            (fun uu___1 ->
               (fun uu___1 ->
                  Obj.magic
                    (genv_push_bv ge
                       (FStar_Reflection_V1_Derived.bv_of_binder b) uu___1
                       abs t)) uu___1)
let (bv_is_shadowed : genv -> FStarC_Reflection_Types.bv -> Prims.bool) =
  fun ge ->
    fun bv ->
      FStar_List_Tot_Base.existsb
        (fun uu___ -> match uu___ with | (b, uu___1) -> bv_eq bv b) ge.svars
let (binder_is_shadowed :
  genv -> FStarC_Reflection_Types.binder -> Prims.bool) =
  fun ge ->
    fun b -> bv_is_shadowed ge (FStar_Reflection_V1_Derived.bv_of_binder b)
let (find_shadowed_bvs :
  genv ->
    FStarC_Reflection_Types.bv Prims.list ->
      (FStarC_Reflection_Types.bv * Prims.bool) Prims.list)
  =
  fun ge ->
    fun bl ->
      FStar_List_Tot_Base.map (fun b -> (b, (bv_is_shadowed ge b))) bl
let (find_shadowed_binders :
  genv ->
    FStarC_Reflection_Types.binder Prims.list ->
      (FStarC_Reflection_Types.binder * Prims.bool) Prims.list)
  =
  fun ge ->
    fun bl ->
      FStar_List_Tot_Base.map (fun b -> (b, (binder_is_shadowed ge b))) bl
let (bv_is_abstract : genv -> FStarC_Reflection_Types.bv -> Prims.bool) =
  fun ge ->
    fun bv ->
      match genv_get ge bv with
      | FStar_Pervasives_Native.None -> false
      | FStar_Pervasives_Native.Some (uu___, abs, uu___1) -> abs
let (binder_is_abstract :
  genv -> FStarC_Reflection_Types.binder -> Prims.bool) =
  fun ge ->
    fun b -> bv_is_abstract ge (FStar_Reflection_V1_Derived.bv_of_binder b)
let (genv_abstract_bvs :
  genv ->
    (FStarC_Reflection_Types.bv * FStarC_Reflection_Types.typ) Prims.list)
  =
  fun ge ->
    FStar_List_Tot_Base.concatMap
      (fun uu___ ->
         match uu___ with
         | (bv, (ty, abs, uu___1)) -> if abs then [(bv, ty)] else []) 
      ge.bmap
let rec (_fresh_bv :
  Prims.string Prims.list ->
    Prims.string ->
      Prims.int ->
        (FStarC_Reflection_Types.bv, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun binder_names ->
    fun basename ->
      fun i ->
        let uu___ =
          Obj.magic
            (FStar_Tactics_Effect.lift_div_tac
               (fun uu___1 -> Prims.strcat basename (Prims.string_of_int i))) in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.InteractiveHelpers.Base.fst"
                   (Prims.of_int (318)) (Prims.of_int (13))
                   (Prims.of_int (318)) (Prims.of_int (39)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.InteractiveHelpers.Base.fst"
                   (Prims.of_int (321)) (Prims.of_int (2))
                   (Prims.of_int (322)) (Prims.of_int (26)))))
          (Obj.magic uu___)
          (fun uu___1 ->
             (fun name ->
                if FStar_List_Tot_Base.mem name binder_names
                then
                  Obj.magic
                    (_fresh_bv binder_names basename (i + Prims.int_one))
                else
                  Obj.magic (FStarC_Tactics_V1_Builtins.fresh_bv_named name))
               uu___1)
let (fresh_bv :
  FStarC_Reflection_Types.env ->
    Prims.string ->
      (FStarC_Reflection_Types.bv, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun e ->
    fun basename ->
      let uu___ =
        Obj.magic
          (FStar_Tactics_Effect.lift_div_tac
             (fun uu___1 -> FStarC_Reflection_V1_Builtins.binders_of_env e)) in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.InteractiveHelpers.Base.fst"
                 (Prims.of_int (325)) (Prims.of_int (16))
                 (Prims.of_int (325)) (Prims.of_int (32)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.InteractiveHelpers.Base.fst"
                 (Prims.of_int (325)) (Prims.of_int (35))
                 (Prims.of_int (327)) (Prims.of_int (35)))))
        (Obj.magic uu___)
        (fun uu___1 ->
           (fun binders ->
              let uu___1 =
                FStar_Tactics_Util.map
                  FStar_Tactics_V1_Derived.name_of_binder binders in
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.InteractiveHelpers.Base.fst"
                            (Prims.of_int (326)) (Prims.of_int (21))
                            (Prims.of_int (326)) (Prims.of_int (55)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.InteractiveHelpers.Base.fst"
                            (Prims.of_int (327)) (Prims.of_int (2))
                            (Prims.of_int (327)) (Prims.of_int (35)))))
                   (Obj.magic uu___1)
                   (fun uu___2 ->
                      (fun binder_names ->
                         Obj.magic
                           (_fresh_bv binder_names basename Prims.int_zero))
                        uu___2))) uu___1)
let (fresh_binder :
  FStarC_Reflection_Types.env ->
    Prims.string ->
      FStarC_Reflection_Types.typ ->
        (FStarC_Reflection_Types.binder, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun e ->
    fun basename ->
      fun ty ->
        let uu___ = fresh_bv e basename in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.InteractiveHelpers.Base.fst"
                   (Prims.of_int (330)) (Prims.of_int (11))
                   (Prims.of_int (330)) (Prims.of_int (30)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.InteractiveHelpers.Base.fst"
                   (Prims.of_int (331)) (Prims.of_int (2))
                   (Prims.of_int (331)) (Prims.of_int (17)))))
          (Obj.magic uu___)
          (fun bv ->
             FStar_Tactics_Effect.lift_div_tac
               (fun uu___1 -> FStar_Reflection_V1_Derived.mk_binder bv ty))
let (genv_push_fresh_binder :
  genv ->
    Prims.string ->
      FStarC_Reflection_Types.typ ->
        ((genv * FStarC_Reflection_Types.binder), unit)
          FStar_Tactics_Effect.tac_repr)
  =
  fun ge ->
    fun basename ->
      fun ty ->
        let uu___ = fresh_binder ge.env basename ty in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.InteractiveHelpers.Base.fst"
                   (Prims.of_int (334)) (Prims.of_int (10))
                   (Prims.of_int (334)) (Prims.of_int (41)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.InteractiveHelpers.Base.fst"
                   (Prims.of_int (334)) (Prims.of_int (44))
                   (Prims.of_int (337)) (Prims.of_int (8)))))
          (Obj.magic uu___)
          (fun uu___1 ->
             (fun b ->
                let uu___1 =
                  genv_push_binder ge b true FStar_Pervasives_Native.None in
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.InteractiveHelpers.Base.fst"
                              (Prims.of_int (336)) (Prims.of_int (12))
                              (Prims.of_int (336)) (Prims.of_int (43)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.InteractiveHelpers.Base.fst"
                              (Prims.of_int (337)) (Prims.of_int (2))
                              (Prims.of_int (337)) (Prims.of_int (8)))))
                     (Obj.magic uu___1)
                     (fun ge' ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___2 -> (ge', b))))) uu___1)
let (push_fresh_binder :
  FStarC_Reflection_Types.env ->
    Prims.string ->
      FStarC_Reflection_Types.typ ->
        ((FStarC_Reflection_Types.env * FStarC_Reflection_Types.binder),
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun e ->
    fun basename ->
      fun ty ->
        let uu___ = fresh_binder e basename ty in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.InteractiveHelpers.Base.fst"
                   (Prims.of_int (341)) (Prims.of_int (10))
                   (Prims.of_int (341)) (Prims.of_int (36)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.InteractiveHelpers.Base.fst"
                   (Prims.of_int (341)) (Prims.of_int (39))
                   (Prims.of_int (343)) (Prims.of_int (7)))))
          (Obj.magic uu___)
          (fun b ->
             FStar_Tactics_Effect.lift_div_tac
               (fun uu___1 ->
                  ((FStarC_Reflection_V1_Builtins.push_binder e b), b)))
let (genv_push_fresh_bv :
  genv ->
    Prims.string ->
      FStarC_Reflection_Types.typ ->
        ((genv * FStarC_Reflection_Types.bv), unit)
          FStar_Tactics_Effect.tac_repr)
  =
  fun ge ->
    fun basename ->
      fun ty ->
        let uu___ = genv_push_fresh_binder ge basename ty in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.InteractiveHelpers.Base.fst"
                   (Prims.of_int (346)) (Prims.of_int (15))
                   (Prims.of_int (346)) (Prims.of_int (52)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.InteractiveHelpers.Base.fst"
                   (Prims.of_int (345)) (Prims.of_int (85))
                   (Prims.of_int (347)) (Prims.of_int (21)))))
          (Obj.magic uu___)
          (fun uu___1 ->
             FStar_Tactics_Effect.lift_div_tac
               (fun uu___2 ->
                  match uu___1 with
                  | (ge', b) ->
                      (ge', (FStar_Reflection_V1_Derived.bv_of_binder b))))
let (push_fresh_var :
  FStarC_Reflection_Types.env ->
    Prims.string ->
      FStarC_Reflection_Types.typ ->
        ((FStarC_Reflection_Types.term * FStarC_Reflection_Types.binder *
           FStarC_Reflection_Types.env),
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun e0 ->
    fun basename ->
      fun ty ->
        let uu___ = push_fresh_binder e0 basename ty in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.InteractiveHelpers.Base.fst"
                   (Prims.of_int (351)) (Prims.of_int (15))
                   (Prims.of_int (351)) (Prims.of_int (47)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.InteractiveHelpers.Base.fst"
                   (Prims.of_int (350)) (Prims.of_int (35))
                   (Prims.of_int (353)) (Prims.of_int (12)))))
          (Obj.magic uu___)
          (fun uu___1 ->
             (fun uu___1 ->
                match uu___1 with
                | (e1, b1) ->
                    let uu___2 =
                      FStarC_Tactics_V1_Builtins.pack
                        (FStarC_Reflection_V1_Data.Tv_Var
                           (FStar_Reflection_V1_Derived.bv_of_binder b1)) in
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.InteractiveHelpers.Base.fst"
                                  (Prims.of_int (352)) (Prims.of_int (11))
                                  (Prims.of_int (352)) (Prims.of_int (42)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.InteractiveHelpers.Base.fst"
                                  (Prims.of_int (353)) (Prims.of_int (2))
                                  (Prims.of_int (353)) (Prims.of_int (12)))))
                         (Obj.magic uu___2)
                         (fun v1 ->
                            FStar_Tactics_Effect.lift_div_tac
                              (fun uu___3 -> (v1, b1, e1))))) uu___1)
let (genv_push_fresh_var :
  genv ->
    Prims.string ->
      FStarC_Reflection_Types.typ ->
        ((FStarC_Reflection_Types.term * FStarC_Reflection_Types.binder *
           genv),
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun ge0 ->
    fun basename ->
      fun ty ->
        let uu___ = genv_push_fresh_binder ge0 basename ty in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.InteractiveHelpers.Base.fst"
                   (Prims.of_int (357)) (Prims.of_int (16))
                   (Prims.of_int (357)) (Prims.of_int (54)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.InteractiveHelpers.Base.fst"
                   (Prims.of_int (356)) (Prims.of_int (41))
                   (Prims.of_int (359)) (Prims.of_int (13)))))
          (Obj.magic uu___)
          (fun uu___1 ->
             (fun uu___1 ->
                match uu___1 with
                | (ge1, b1) ->
                    let uu___2 =
                      FStarC_Tactics_V1_Builtins.pack
                        (FStarC_Reflection_V1_Data.Tv_Var
                           (FStar_Reflection_V1_Derived.bv_of_binder b1)) in
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.InteractiveHelpers.Base.fst"
                                  (Prims.of_int (358)) (Prims.of_int (11))
                                  (Prims.of_int (358)) (Prims.of_int (42)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.InteractiveHelpers.Base.fst"
                                  (Prims.of_int (359)) (Prims.of_int (2))
                                  (Prims.of_int (359)) (Prims.of_int (13)))))
                         (Obj.magic uu___2)
                         (fun v1 ->
                            FStar_Tactics_Effect.lift_div_tac
                              (fun uu___3 -> (v1, b1, ge1))))) uu___1)
let (push_two_fresh_vars :
  FStarC_Reflection_Types.env ->
    Prims.string ->
      FStarC_Reflection_Types.typ ->
        ((FStarC_Reflection_Types.term * FStarC_Reflection_Types.binder *
           FStarC_Reflection_Types.term * FStarC_Reflection_Types.binder *
           FStarC_Reflection_Types.env),
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun e0 ->
    fun basename ->
      fun ty ->
        let uu___ = push_fresh_binder e0 basename ty in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.InteractiveHelpers.Base.fst"
                   (Prims.of_int (363)) (Prims.of_int (15))
                   (Prims.of_int (363)) (Prims.of_int (47)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.InteractiveHelpers.Base.fst"
                   (Prims.of_int (362)) (Prims.of_int (40))
                   (Prims.of_int (367)) (Prims.of_int (20)))))
          (Obj.magic uu___)
          (fun uu___1 ->
             (fun uu___1 ->
                match uu___1 with
                | (e1, b1) ->
                    let uu___2 = push_fresh_binder e1 basename ty in
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.InteractiveHelpers.Base.fst"
                                  (Prims.of_int (364)) (Prims.of_int (15))
                                  (Prims.of_int (364)) (Prims.of_int (47)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.InteractiveHelpers.Base.fst"
                                  (Prims.of_int (363)) (Prims.of_int (50))
                                  (Prims.of_int (367)) (Prims.of_int (20)))))
                         (Obj.magic uu___2)
                         (fun uu___3 ->
                            (fun uu___3 ->
                               match uu___3 with
                               | (e2, b2) ->
                                   let uu___4 =
                                     FStarC_Tactics_V1_Builtins.pack
                                       (FStarC_Reflection_V1_Data.Tv_Var
                                          (FStar_Reflection_V1_Derived.bv_of_binder
                                             b1)) in
                                   Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "FStar.InteractiveHelpers.Base.fst"
                                                 (Prims.of_int (365))
                                                 (Prims.of_int (11))
                                                 (Prims.of_int (365))
                                                 (Prims.of_int (42)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "FStar.InteractiveHelpers.Base.fst"
                                                 (Prims.of_int (365))
                                                 (Prims.of_int (45))
                                                 (Prims.of_int (367))
                                                 (Prims.of_int (20)))))
                                        (Obj.magic uu___4)
                                        (fun uu___5 ->
                                           (fun v1 ->
                                              let uu___5 =
                                                FStarC_Tactics_V1_Builtins.pack
                                                  (FStarC_Reflection_V1_Data.Tv_Var
                                                     (FStar_Reflection_V1_Derived.bv_of_binder
                                                        b2)) in
                                              Obj.magic
                                                (FStar_Tactics_Effect.tac_bind
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "FStar.InteractiveHelpers.Base.fst"
                                                            (Prims.of_int (366))
                                                            (Prims.of_int (11))
                                                            (Prims.of_int (366))
                                                            (Prims.of_int (42)))))
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "FStar.InteractiveHelpers.Base.fst"
                                                            (Prims.of_int (367))
                                                            (Prims.of_int (2))
                                                            (Prims.of_int (367))
                                                            (Prims.of_int (20)))))
                                                   (Obj.magic uu___5)
                                                   (fun v2 ->
                                                      FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___6 ->
                                                           (v1, b1, v2, b2,
                                                             e2))))) uu___5)))
                              uu___3))) uu___1)
let (genv_push_two_fresh_vars :
  genv ->
    Prims.string ->
      FStarC_Reflection_Types.typ ->
        ((FStarC_Reflection_Types.term * FStarC_Reflection_Types.binder *
           FStarC_Reflection_Types.term * FStarC_Reflection_Types.binder *
           genv),
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun ge0 ->
    fun basename ->
      fun ty ->
        let uu___ = genv_push_fresh_binder ge0 basename ty in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.InteractiveHelpers.Base.fst"
                   (Prims.of_int (371)) (Prims.of_int (16))
                   (Prims.of_int (371)) (Prims.of_int (54)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.InteractiveHelpers.Base.fst"
                   (Prims.of_int (370)) (Prims.of_int (46))
                   (Prims.of_int (375)) (Prims.of_int (21)))))
          (Obj.magic uu___)
          (fun uu___1 ->
             (fun uu___1 ->
                match uu___1 with
                | (ge1, b1) ->
                    let uu___2 = genv_push_fresh_binder ge1 basename ty in
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.InteractiveHelpers.Base.fst"
                                  (Prims.of_int (372)) (Prims.of_int (16))
                                  (Prims.of_int (372)) (Prims.of_int (54)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.InteractiveHelpers.Base.fst"
                                  (Prims.of_int (371)) (Prims.of_int (57))
                                  (Prims.of_int (375)) (Prims.of_int (21)))))
                         (Obj.magic uu___2)
                         (fun uu___3 ->
                            (fun uu___3 ->
                               match uu___3 with
                               | (ge2, b2) ->
                                   let uu___4 =
                                     FStarC_Tactics_V1_Builtins.pack
                                       (FStarC_Reflection_V1_Data.Tv_Var
                                          (FStar_Reflection_V1_Derived.bv_of_binder
                                             b1)) in
                                   Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "FStar.InteractiveHelpers.Base.fst"
                                                 (Prims.of_int (373))
                                                 (Prims.of_int (11))
                                                 (Prims.of_int (373))
                                                 (Prims.of_int (42)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "FStar.InteractiveHelpers.Base.fst"
                                                 (Prims.of_int (373))
                                                 (Prims.of_int (45))
                                                 (Prims.of_int (375))
                                                 (Prims.of_int (21)))))
                                        (Obj.magic uu___4)
                                        (fun uu___5 ->
                                           (fun v1 ->
                                              let uu___5 =
                                                FStarC_Tactics_V1_Builtins.pack
                                                  (FStarC_Reflection_V1_Data.Tv_Var
                                                     (FStar_Reflection_V1_Derived.bv_of_binder
                                                        b2)) in
                                              Obj.magic
                                                (FStar_Tactics_Effect.tac_bind
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "FStar.InteractiveHelpers.Base.fst"
                                                            (Prims.of_int (374))
                                                            (Prims.of_int (11))
                                                            (Prims.of_int (374))
                                                            (Prims.of_int (42)))))
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "FStar.InteractiveHelpers.Base.fst"
                                                            (Prims.of_int (375))
                                                            (Prims.of_int (2))
                                                            (Prims.of_int (375))
                                                            (Prims.of_int (21)))))
                                                   (Obj.magic uu___5)
                                                   (fun v2 ->
                                                      FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___6 ->
                                                           (v1, b1, v2, b2,
                                                             ge2))))) uu___5)))
                              uu___3))) uu___1)
let (norm_apply_subst :
  FStarC_Reflection_Types.env ->
    FStarC_Reflection_Types.term ->
      ((FStarC_Reflection_Types.bv * FStarC_Reflection_Types.typ) *
        FStarC_Reflection_Types.term) Prims.list ->
        (FStarC_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun e ->
    fun t ->
      fun subst ->
        let uu___ =
          Obj.magic
            (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> unzip subst)) in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.InteractiveHelpers.Base.fst"
                   (Prims.of_int (389)) (Prims.of_int (15))
                   (Prims.of_int (389)) (Prims.of_int (26)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.InteractiveHelpers.Base.fst"
                   (Prims.of_int (388)) (Prims.of_int (32))
                   (Prims.of_int (393)) (Prims.of_int (23)))))
          (Obj.magic uu___)
          (fun uu___1 ->
             (fun uu___1 ->
                match uu___1 with
                | (bl, vl) ->
                    let uu___2 =
                      Obj.magic
                        (FStar_Tactics_Effect.lift_div_tac
                           (fun uu___3 ->
                              FStar_List_Tot_Base.map
                                (fun uu___4 ->
                                   match uu___4 with
                                   | (bv, ty) ->
                                       FStar_Reflection_V1_Derived.mk_binder
                                         bv ty) bl)) in
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.InteractiveHelpers.Base.fst"
                                  (Prims.of_int (390)) (Prims.of_int (11))
                                  (Prims.of_int (390)) (Prims.of_int (59)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.InteractiveHelpers.Base.fst"
                                  (Prims.of_int (390)) (Prims.of_int (62))
                                  (Prims.of_int (393)) (Prims.of_int (23)))))
                         (Obj.magic uu___2)
                         (fun uu___3 ->
                            (fun bl1 ->
                               let uu___3 =
                                 FStar_Tactics_V1_Derived.mk_abs bl1 t in
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.InteractiveHelpers.Base.fst"
                                             (Prims.of_int (391))
                                             (Prims.of_int (11))
                                             (Prims.of_int (391))
                                             (Prims.of_int (22)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.InteractiveHelpers.Base.fst"
                                             (Prims.of_int (391))
                                             (Prims.of_int (25))
                                             (Prims.of_int (393))
                                             (Prims.of_int (23)))))
                                    (Obj.magic uu___3)
                                    (fun uu___4 ->
                                       (fun t1 ->
                                          let uu___4 =
                                            Obj.magic
                                              (FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___5 ->
                                                    FStar_Reflection_V1_Derived.mk_e_app
                                                      t1 vl)) in
                                          Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "FStar.InteractiveHelpers.Base.fst"
                                                        (Prims.of_int (392))
                                                        (Prims.of_int (11))
                                                        (Prims.of_int (392))
                                                        (Prims.of_int (25)))))
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "FStar.InteractiveHelpers.Base.fst"
                                                        (Prims.of_int (393))
                                                        (Prims.of_int (2))
                                                        (Prims.of_int (393))
                                                        (Prims.of_int (23)))))
                                               (Obj.magic uu___4)
                                               (fun uu___5 ->
                                                  (fun t2 ->
                                                     Obj.magic
                                                       (FStarC_Tactics_V1_Builtins.norm_term_env
                                                          e [] t2)) uu___5)))
                                         uu___4))) uu___3))) uu___1)
let (norm_apply_subst_in_comp :
  FStarC_Reflection_Types.env ->
    FStarC_Reflection_Types.comp ->
      ((FStarC_Reflection_Types.bv * FStarC_Reflection_Types.typ) *
        FStarC_Reflection_Types.term) Prims.list ->
        (FStarC_Reflection_Types.comp, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun e ->
    fun c ->
      fun subst ->
        let uu___ =
          Obj.magic
            (FStar_Tactics_Effect.lift_div_tac
               (fun uu___1 -> fun x -> norm_apply_subst e x subst)) in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.InteractiveHelpers.Base.fst"
                   (Prims.of_int (396)) (Prims.of_int (14))
                   (Prims.of_int (396)) (Prims.of_int (51)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.InteractiveHelpers.Base.fst"
                   (Prims.of_int (396)) (Prims.of_int (54))
                   (Prims.of_int (419)) (Prims.of_int (55)))))
          (Obj.magic uu___)
          (fun uu___1 ->
             (fun subst1 ->
                let uu___1 =
                  Obj.magic
                    (FStar_Tactics_Effect.lift_div_tac
                       (fun uu___3 ->
                          fun uu___2 ->
                            (fun uu___2 ->
                               fun a ->
                                 match a with
                                 | FStarC_Reflection_V1_Data.Q_Implicit ->
                                     Obj.magic
                                       (Obj.repr
                                          (FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___3 -> a)))
                                 | FStarC_Reflection_V1_Data.Q_Explicit ->
                                     Obj.magic
                                       (Obj.repr
                                          (FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___3 -> a)))
                                 | FStarC_Reflection_V1_Data.Q_Meta t ->
                                     Obj.magic
                                       (Obj.repr
                                          (let uu___3 = subst1 t in
                                           FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "FStar.InteractiveHelpers.Base.fst"
                                                      (Prims.of_int (401))
                                                      (Prims.of_int (25))
                                                      (Prims.of_int (401))
                                                      (Prims.of_int (34)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "FStar.InteractiveHelpers.Base.fst"
                                                      (Prims.of_int (401))
                                                      (Prims.of_int (18))
                                                      (Prims.of_int (401))
                                                      (Prims.of_int (34)))))
                                             (Obj.magic uu___3)
                                             (fun uu___4 ->
                                                FStar_Tactics_Effect.lift_div_tac
                                                  (fun uu___5 ->
                                                     FStarC_Reflection_V1_Data.Q_Meta
                                                       uu___4))))) uu___3
                              uu___2)) in
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.InteractiveHelpers.Base.fst"
                              (Prims.of_int (398)) (Prims.of_int (4))
                              (Prims.of_int (401)) (Prims.of_int (34)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.InteractiveHelpers.Base.fst"
                              (Prims.of_int (403)) (Prims.of_int (2))
                              (Prims.of_int (419)) (Prims.of_int (55)))))
                     (Obj.magic uu___1)
                     (fun uu___2 ->
                        (fun subst_in_aqualv ->
                           match FStarC_Reflection_V1_Builtins.inspect_comp c
                           with
                           | FStarC_Reflection_V1_Data.C_Total ret ->
                               let uu___2 = subst1 ret in
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.InteractiveHelpers.Base.fst"
                                             (Prims.of_int (405))
                                             (Prims.of_int (14))
                                             (Prims.of_int (405))
                                             (Prims.of_int (23)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.InteractiveHelpers.Base.fst"
                                             (Prims.of_int (406))
                                             (Prims.of_int (4))
                                             (Prims.of_int (406))
                                             (Prims.of_int (27)))))
                                    (Obj.magic uu___2)
                                    (fun ret1 ->
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___3 ->
                                            FStarC_Reflection_V1_Builtins.pack_comp
                                              (FStarC_Reflection_V1_Data.C_Total
                                                 ret1))))
                           | FStarC_Reflection_V1_Data.C_GTotal ret ->
                               let uu___2 = subst1 ret in
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.InteractiveHelpers.Base.fst"
                                             (Prims.of_int (408))
                                             (Prims.of_int (14))
                                             (Prims.of_int (408))
                                             (Prims.of_int (23)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.InteractiveHelpers.Base.fst"
                                             (Prims.of_int (409))
                                             (Prims.of_int (4))
                                             (Prims.of_int (409))
                                             (Prims.of_int (28)))))
                                    (Obj.magic uu___2)
                                    (fun ret1 ->
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___3 ->
                                            FStarC_Reflection_V1_Builtins.pack_comp
                                              (FStarC_Reflection_V1_Data.C_GTotal
                                                 ret1))))
                           | FStarC_Reflection_V1_Data.C_Lemma
                               (pre, post, patterns) ->
                               let uu___2 = subst1 pre in
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.InteractiveHelpers.Base.fst"
                                             (Prims.of_int (411))
                                             (Prims.of_int (14))
                                             (Prims.of_int (411))
                                             (Prims.of_int (23)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.InteractiveHelpers.Base.fst"
                                             (Prims.of_int (411))
                                             (Prims.of_int (26))
                                             (Prims.of_int (414))
                                             (Prims.of_int (41)))))
                                    (Obj.magic uu___2)
                                    (fun uu___3 ->
                                       (fun pre1 ->
                                          let uu___3 = subst1 post in
                                          Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "FStar.InteractiveHelpers.Base.fst"
                                                        (Prims.of_int (412))
                                                        (Prims.of_int (15))
                                                        (Prims.of_int (412))
                                                        (Prims.of_int (25)))))
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "FStar.InteractiveHelpers.Base.fst"
                                                        (Prims.of_int (412))
                                                        (Prims.of_int (28))
                                                        (Prims.of_int (414))
                                                        (Prims.of_int (41)))))
                                               (Obj.magic uu___3)
                                               (fun uu___4 ->
                                                  (fun post1 ->
                                                     let uu___4 =
                                                       subst1 patterns in
                                                     Obj.magic
                                                       (FStar_Tactics_Effect.tac_bind
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "FStar.InteractiveHelpers.Base.fst"
                                                                   (Prims.of_int (413))
                                                                   (Prims.of_int (19))
                                                                   (Prims.of_int (413))
                                                                   (Prims.of_int (33)))))
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "FStar.InteractiveHelpers.Base.fst"
                                                                   (Prims.of_int (414))
                                                                   (Prims.of_int (4))
                                                                   (Prims.of_int (414))
                                                                   (Prims.of_int (41)))))
                                                          (Obj.magic uu___4)
                                                          (fun patterns1 ->
                                                             FStar_Tactics_Effect.lift_div_tac
                                                               (fun uu___5 ->
                                                                  FStarC_Reflection_V1_Builtins.pack_comp
                                                                    (
                                                                    FStarC_Reflection_V1_Data.C_Lemma
                                                                    (pre1,
                                                                    post1,
                                                                    patterns1))))))
                                                    uu___4))) uu___3))
                           | FStarC_Reflection_V1_Data.C_Eff
                               (us, eff_name, result, eff_args, decrs) ->
                               let uu___2 = subst1 result in
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.InteractiveHelpers.Base.fst"
                                             (Prims.of_int (416))
                                             (Prims.of_int (17))
                                             (Prims.of_int (416))
                                             (Prims.of_int (29)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.InteractiveHelpers.Base.fst"
                                             (Prims.of_int (416))
                                             (Prims.of_int (32))
                                             (Prims.of_int (419))
                                             (Prims.of_int (55)))))
                                    (Obj.magic uu___2)
                                    (fun uu___3 ->
                                       (fun result1 ->
                                          let uu___3 =
                                            FStar_Tactics_Util.map
                                              (fun uu___4 ->
                                                 match uu___4 with
                                                 | (x, a) ->
                                                     let uu___5 = subst1 x in
                                                     FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "FStar.InteractiveHelpers.Base.fst"
                                                                (Prims.of_int (417))
                                                                (Prims.of_int (39))
                                                                (Prims.of_int (417))
                                                                (Prims.of_int (46)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "FStar.InteractiveHelpers.Base.fst"
                                                                (Prims.of_int (417))
                                                                (Prims.of_int (38))
                                                                (Prims.of_int (417))
                                                                (Prims.of_int (66)))))
                                                       (Obj.magic uu___5)
                                                       (fun uu___6 ->
                                                          (fun uu___6 ->
                                                             let uu___7 =
                                                               subst_in_aqualv
                                                                 a in
                                                             Obj.magic
                                                               (FStar_Tactics_Effect.tac_bind
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (417))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (417))
                                                                    (Prims.of_int (65)))))
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (417))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (417))
                                                                    (Prims.of_int (66)))))
                                                                  (Obj.magic
                                                                    uu___7)
                                                                  (fun uu___8
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    (uu___6,
                                                                    uu___8)))))
                                                            uu___6)) eff_args in
                                          Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "FStar.InteractiveHelpers.Base.fst"
                                                        (Prims.of_int (417))
                                                        (Prims.of_int (19))
                                                        (Prims.of_int (417))
                                                        (Prims.of_int (76)))))
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "FStar.InteractiveHelpers.Base.fst"
                                                        (Prims.of_int (417))
                                                        (Prims.of_int (79))
                                                        (Prims.of_int (419))
                                                        (Prims.of_int (55)))))
                                               (Obj.magic uu___3)
                                               (fun uu___4 ->
                                                  (fun eff_args1 ->
                                                     let uu___4 =
                                                       FStar_Tactics_Util.map
                                                         subst1 decrs in
                                                     Obj.magic
                                                       (FStar_Tactics_Effect.tac_bind
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "FStar.InteractiveHelpers.Base.fst"
                                                                   (Prims.of_int (418))
                                                                   (Prims.of_int (16))
                                                                   (Prims.of_int (418))
                                                                   (Prims.of_int (31)))))
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "FStar.InteractiveHelpers.Base.fst"
                                                                   (Prims.of_int (419))
                                                                   (Prims.of_int (4))
                                                                   (Prims.of_int (419))
                                                                   (Prims.of_int (55)))))
                                                          (Obj.magic uu___4)
                                                          (fun decrs1 ->
                                                             FStar_Tactics_Effect.lift_div_tac
                                                               (fun uu___5 ->
                                                                  FStarC_Reflection_V1_Builtins.pack_comp
                                                                    (
                                                                    FStarC_Reflection_V1_Data.C_Eff
                                                                    (us,
                                                                    eff_name,
                                                                    result1,
                                                                    eff_args1,
                                                                    decrs1))))))
                                                    uu___4))) uu___3)))
                          uu___2))) uu___1)
let rec (deep_apply_subst :
  FStarC_Reflection_Types.env ->
    FStarC_Reflection_Types.term ->
      (FStarC_Reflection_Types.bv * FStarC_Reflection_Types.term) Prims.list
        -> (FStarC_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun e ->
    fun t ->
      fun subst ->
        let uu___ = FStarC_Tactics_V1_Builtins.inspect t in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.InteractiveHelpers.Base.fst"
                   (Prims.of_int (438)) (Prims.of_int (8))
                   (Prims.of_int (438)) (Prims.of_int (17)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.InteractiveHelpers.Base.fst"
                   (Prims.of_int (438)) (Prims.of_int (2))
                   (Prims.of_int (513)) (Prims.of_int (5)))))
          (Obj.magic uu___)
          (fun uu___1 ->
             (fun uu___1 ->
                match uu___1 with
                | FStarC_Reflection_V1_Data.Tv_Var b ->
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___2 ->
                               match bind_map_get subst b with
                               | FStar_Pervasives_Native.None -> t
                               | FStar_Pervasives_Native.Some t' -> t')))
                | FStarC_Reflection_V1_Data.Tv_BVar b ->
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___2 ->
                               match bind_map_get subst b with
                               | FStar_Pervasives_Native.None -> t
                               | FStar_Pervasives_Native.Some t' -> t')))
                | FStarC_Reflection_V1_Data.Tv_FVar uu___2 ->
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_Effect.lift_div_tac (fun uu___3 -> t)))
                | FStarC_Reflection_V1_Data.Tv_App (hd, (a, qual)) ->
                    Obj.magic
                      (Obj.repr
                         (let uu___2 = deep_apply_subst e hd subst in
                          FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.InteractiveHelpers.Base.fst"
                                     (Prims.of_int (452)) (Prims.of_int (13))
                                     (Prims.of_int (452)) (Prims.of_int (40)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.InteractiveHelpers.Base.fst"
                                     (Prims.of_int (452)) (Prims.of_int (43))
                                     (Prims.of_int (454)) (Prims.of_int (30)))))
                            (Obj.magic uu___2)
                            (fun uu___3 ->
                               (fun hd1 ->
                                  let uu___3 = deep_apply_subst e a subst in
                                  Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.InteractiveHelpers.Base.fst"
                                                (Prims.of_int (453))
                                                (Prims.of_int (12))
                                                (Prims.of_int (453))
                                                (Prims.of_int (38)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.InteractiveHelpers.Base.fst"
                                                (Prims.of_int (454))
                                                (Prims.of_int (4))
                                                (Prims.of_int (454))
                                                (Prims.of_int (30)))))
                                       (Obj.magic uu___3)
                                       (fun uu___4 ->
                                          (fun a1 ->
                                             Obj.magic
                                               (FStarC_Tactics_V1_Builtins.pack
                                                  (FStarC_Reflection_V1_Data.Tv_App
                                                     (hd1, (a1, qual)))))
                                            uu___4))) uu___3)))
                | FStarC_Reflection_V1_Data.Tv_Abs (br, body) ->
                    Obj.magic
                      (Obj.repr
                         (let uu___2 = deep_apply_subst e body subst in
                          FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.InteractiveHelpers.Base.fst"
                                     (Prims.of_int (456)) (Prims.of_int (15))
                                     (Prims.of_int (456)) (Prims.of_int (44)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.InteractiveHelpers.Base.fst"
                                     (Prims.of_int (457)) (Prims.of_int (4))
                                     (Prims.of_int (457)) (Prims.of_int (25)))))
                            (Obj.magic uu___2)
                            (fun uu___3 ->
                               (fun body1 ->
                                  Obj.magic
                                    (FStarC_Tactics_V1_Builtins.pack
                                       (FStarC_Reflection_V1_Data.Tv_Abs
                                          (br, body1)))) uu___3)))
                | FStarC_Reflection_V1_Data.Tv_Arrow (br, c) ->
                    Obj.magic
                      (Obj.repr
                         (let uu___2 = deep_apply_subst_in_binder e br subst in
                          FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.InteractiveHelpers.Base.fst"
                                     (Prims.of_int (459)) (Prims.of_int (20))
                                     (Prims.of_int (459)) (Prims.of_int (57)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.InteractiveHelpers.Base.fst"
                                     (Prims.of_int (458)) (Prims.of_int (20))
                                     (Prims.of_int (461)) (Prims.of_int (24)))))
                            (Obj.magic uu___2)
                            (fun uu___3 ->
                               (fun uu___3 ->
                                  match uu___3 with
                                  | (br1, subst1) ->
                                      let uu___4 =
                                        deep_apply_subst_in_comp e c subst1 in
                                      Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "FStar.InteractiveHelpers.Base.fst"
                                                    (Prims.of_int (460))
                                                    (Prims.of_int (12))
                                                    (Prims.of_int (460))
                                                    (Prims.of_int (46)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "FStar.InteractiveHelpers.Base.fst"
                                                    (Prims.of_int (461))
                                                    (Prims.of_int (4))
                                                    (Prims.of_int (461))
                                                    (Prims.of_int (24)))))
                                           (Obj.magic uu___4)
                                           (fun uu___5 ->
                                              (fun c1 ->
                                                 Obj.magic
                                                   (FStarC_Tactics_V1_Builtins.pack
                                                      (FStarC_Reflection_V1_Data.Tv_Arrow
                                                         (br1, c1)))) uu___5)))
                                 uu___3)))
                | FStarC_Reflection_V1_Data.Tv_Type uu___2 ->
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_Effect.lift_div_tac (fun uu___3 -> t)))
                | FStarC_Reflection_V1_Data.Tv_Refine (bv, sort, ref) ->
                    Obj.magic
                      (Obj.repr
                         (let uu___2 = deep_apply_subst e sort subst in
                          FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.InteractiveHelpers.Base.fst"
                                     (Prims.of_int (464)) (Prims.of_int (15))
                                     (Prims.of_int (464)) (Prims.of_int (44)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.InteractiveHelpers.Base.fst"
                                     (Prims.of_int (464)) (Prims.of_int (47))
                                     (Prims.of_int (467)) (Prims.of_int (32)))))
                            (Obj.magic uu___2)
                            (fun uu___3 ->
                               (fun sort1 ->
                                  let uu___3 =
                                    deep_apply_subst_in_bv e bv subst in
                                  Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.InteractiveHelpers.Base.fst"
                                                (Prims.of_int (465))
                                                (Prims.of_int (20))
                                                (Prims.of_int (465))
                                                (Prims.of_int (53)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.InteractiveHelpers.Base.fst"
                                                (Prims.of_int (464))
                                                (Prims.of_int (47))
                                                (Prims.of_int (467))
                                                (Prims.of_int (32)))))
                                       (Obj.magic uu___3)
                                       (fun uu___4 ->
                                          (fun uu___4 ->
                                             match uu___4 with
                                             | (bv1, subst1) ->
                                                 let uu___5 =
                                                   deep_apply_subst e ref
                                                     subst1 in
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "FStar.InteractiveHelpers.Base.fst"
                                                               (Prims.of_int (466))
                                                               (Prims.of_int (14))
                                                               (Prims.of_int (466))
                                                               (Prims.of_int (42)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "FStar.InteractiveHelpers.Base.fst"
                                                               (Prims.of_int (467))
                                                               (Prims.of_int (4))
                                                               (Prims.of_int (467))
                                                               (Prims.of_int (32)))))
                                                      (Obj.magic uu___5)
                                                      (fun uu___6 ->
                                                         (fun ref1 ->
                                                            Obj.magic
                                                              (FStarC_Tactics_V1_Builtins.pack
                                                                 (FStarC_Reflection_V1_Data.Tv_Refine
                                                                    (bv1,
                                                                    sort1,
                                                                    ref1))))
                                                           uu___6))) uu___4)))
                                 uu___3)))
                | FStarC_Reflection_V1_Data.Tv_Const uu___2 ->
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_Effect.lift_div_tac (fun uu___3 -> t)))
                | FStarC_Reflection_V1_Data.Tv_Uvar (uu___2, uu___3) ->
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_Effect.lift_div_tac (fun uu___4 -> t)))
                | FStarC_Reflection_V1_Data.Tv_Let
                    (recf, attrs, bv, ty, def, body) ->
                    Obj.magic
                      (Obj.repr
                         (let uu___2 = deep_apply_subst e ty subst in
                          FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.InteractiveHelpers.Base.fst"
                                     (Prims.of_int (472)) (Prims.of_int (13))
                                     (Prims.of_int (472)) (Prims.of_int (40)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.InteractiveHelpers.Base.fst"
                                     (Prims.of_int (472)) (Prims.of_int (43))
                                     (Prims.of_int (476)) (Prims.of_int (40)))))
                            (Obj.magic uu___2)
                            (fun uu___3 ->
                               (fun ty1 ->
                                  let uu___3 = deep_apply_subst e def subst in
                                  Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.InteractiveHelpers.Base.fst"
                                                (Prims.of_int (473))
                                                (Prims.of_int (14))
                                                (Prims.of_int (473))
                                                (Prims.of_int (42)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.InteractiveHelpers.Base.fst"
                                                (Prims.of_int (473))
                                                (Prims.of_int (45))
                                                (Prims.of_int (476))
                                                (Prims.of_int (40)))))
                                       (Obj.magic uu___3)
                                       (fun uu___4 ->
                                          (fun def1 ->
                                             let uu___4 =
                                               deep_apply_subst_in_bv e bv
                                                 subst in
                                             Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.InteractiveHelpers.Base.fst"
                                                           (Prims.of_int (474))
                                                           (Prims.of_int (20))
                                                           (Prims.of_int (474))
                                                           (Prims.of_int (53)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.InteractiveHelpers.Base.fst"
                                                           (Prims.of_int (473))
                                                           (Prims.of_int (45))
                                                           (Prims.of_int (476))
                                                           (Prims.of_int (40)))))
                                                  (Obj.magic uu___4)
                                                  (fun uu___5 ->
                                                     (fun uu___5 ->
                                                        match uu___5 with
                                                        | (bv1, subst1) ->
                                                            let uu___6 =
                                                              deep_apply_subst
                                                                e body subst1 in
                                                            Obj.magic
                                                              (FStar_Tactics_Effect.tac_bind
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (475))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (475))
                                                                    (Prims.of_int (44)))))
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (476))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (476))
                                                                    (Prims.of_int (40)))))
                                                                 (Obj.magic
                                                                    uu___6)
                                                                 (fun uu___7
                                                                    ->
                                                                    (fun
                                                                    body1 ->
                                                                    Obj.magic
                                                                    (FStarC_Tactics_V1_Builtins.pack
                                                                    (FStarC_Reflection_V1_Data.Tv_Let
                                                                    (recf,
                                                                    [], bv1,
                                                                    ty1,
                                                                    def1,
                                                                    body1))))
                                                                    uu___7)))
                                                       uu___5))) uu___4)))
                                 uu___3)))
                | FStarC_Reflection_V1_Data.Tv_Match
                    (scrutinee, ret_opt, branches) ->
                    Obj.magic
                      (Obj.repr
                         (let uu___2 = deep_apply_subst e scrutinee subst in
                          FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.InteractiveHelpers.Base.fst"
                                     (Prims.of_int (478)) (Prims.of_int (20))
                                     (Prims.of_int (478)) (Prims.of_int (54)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.InteractiveHelpers.Base.fst"
                                     (Prims.of_int (478)) (Prims.of_int (57))
                                     (Prims.of_int (500)) (Prims.of_int (46)))))
                            (Obj.magic uu___2)
                            (fun uu___3 ->
                               (fun scrutinee1 ->
                                  let uu___3 =
                                    FStar_Tactics_Util.map_opt
                                      (fun uu___4 ->
                                         match uu___4 with
                                         | (b, asc) ->
                                             let uu___5 =
                                               deep_apply_subst_in_binder e b
                                                 subst in
                                             FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "FStar.InteractiveHelpers.Base.fst"
                                                        (Prims.of_int (480))
                                                        (Prims.of_int (21))
                                                        (Prims.of_int (480))
                                                        (Prims.of_int (57)))))
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "FStar.InteractiveHelpers.Base.fst"
                                                        (Prims.of_int (479))
                                                        (Prims.of_int (42))
                                                        (Prims.of_int (491))
                                                        (Prims.of_int (12)))))
                                               (Obj.magic uu___5)
                                               (fun uu___6 ->
                                                  (fun uu___6 ->
                                                     match uu___6 with
                                                     | (b1, subst1) ->
                                                         let uu___7 =
                                                           match asc with
                                                           | (FStar_Pervasives.Inl
                                                              t1, tacopt,
                                                              use_eq) ->
                                                               let uu___8 =
                                                                 let uu___9 =
                                                                   deep_apply_subst
                                                                    e t1
                                                                    subst1 in
                                                                 FStar_Tactics_Effect.tac_bind
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (484))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (484))
                                                                    (Prims.of_int (42)))))
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (484))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (484))
                                                                    (Prims.of_int (42)))))
                                                                   (Obj.magic
                                                                    uu___9)
                                                                   (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Pervasives.Inl
                                                                    uu___10)) in
                                                               FStar_Tactics_Effect.tac_bind
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (484))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (484))
                                                                    (Prims.of_int (42)))))
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (484))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (486))
                                                                    (Prims.of_int (16)))))
                                                                 (Obj.magic
                                                                    uu___8)
                                                                 (fun uu___9
                                                                    ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    let uu___10
                                                                    =
                                                                    FStar_Tactics_Util.map_opt
                                                                    (fun tac
                                                                    ->
                                                                    deep_apply_subst
                                                                    e tac
                                                                    subst1)
                                                                    tacopt in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (485))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (485))
                                                                    (Prims.of_int (66)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (484))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (486))
                                                                    (Prims.of_int (16)))))
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
                                                                    uu___11,
                                                                    use_eq)))))
                                                                    uu___9)
                                                           | (FStar_Pervasives.Inr
                                                              c, tacopt,
                                                              use_eq) ->
                                                               let uu___8 =
                                                                 let uu___9 =
                                                                   deep_apply_subst_in_comp
                                                                    e c
                                                                    subst1 in
                                                                 FStar_Tactics_Effect.tac_bind
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (488))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (488))
                                                                    (Prims.of_int (50)))))
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (488))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (488))
                                                                    (Prims.of_int (50)))))
                                                                   (Obj.magic
                                                                    uu___9)
                                                                   (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Pervasives.Inr
                                                                    uu___10)) in
                                                               FStar_Tactics_Effect.tac_bind
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (488))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (488))
                                                                    (Prims.of_int (50)))))
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (488))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (490))
                                                                    (Prims.of_int (16)))))
                                                                 (Obj.magic
                                                                    uu___8)
                                                                 (fun uu___9
                                                                    ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    let uu___10
                                                                    =
                                                                    FStar_Tactics_Util.map_opt
                                                                    (fun tac
                                                                    ->
                                                                    deep_apply_subst
                                                                    e tac
                                                                    subst1)
                                                                    tacopt in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (489))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (489))
                                                                    (Prims.of_int (66)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (488))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (490))
                                                                    (Prims.of_int (16)))))
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
                                                                    uu___11,
                                                                    use_eq)))))
                                                                    uu___9) in
                                                         Obj.magic
                                                           (FStar_Tactics_Effect.tac_bind
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (482))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (490))
                                                                    (Prims.of_int (16)))))
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (491))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (491))
                                                                    (Prims.of_int (12)))))
                                                              (Obj.magic
                                                                 uu___7)
                                                              (fun asc1 ->
                                                                 FStar_Tactics_Effect.lift_div_tac
                                                                   (fun
                                                                    uu___8 ->
                                                                    (b1,
                                                                    asc1)))))
                                                    uu___6)) ret_opt in
                                  Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.InteractiveHelpers.Base.fst"
                                                (Prims.of_int (479))
                                                (Prims.of_int (18))
                                                (Prims.of_int (491))
                                                (Prims.of_int (21)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.InteractiveHelpers.Base.fst"
                                                (Prims.of_int (491))
                                                (Prims.of_int (24))
                                                (Prims.of_int (500))
                                                (Prims.of_int (46)))))
                                       (Obj.magic uu___3)
                                       (fun uu___4 ->
                                          (fun ret_opt1 ->
                                             let uu___4 =
                                               Obj.magic
                                                 (FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___5 ->
                                                       fun branch ->
                                                         let uu___6 =
                                                           Obj.magic
                                                             (FStar_Tactics_Effect.lift_div_tac
                                                                (fun uu___7
                                                                   -> branch)) in
                                                         FStar_Tactics_Effect.tac_bind
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (494))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (494))
                                                                    (Prims.of_int (26)))))
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (493))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (497))
                                                                    (Prims.of_int (13)))))
                                                           (Obj.magic uu___6)
                                                           (fun uu___7 ->
                                                              (fun uu___7 ->
                                                                 match uu___7
                                                                 with
                                                                 | (pat, tm)
                                                                    ->
                                                                    let uu___8
                                                                    =
                                                                    deep_apply_subst_in_pattern
                                                                    e pat
                                                                    subst in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (495))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (495))
                                                                    (Prims.of_int (62)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (494))
                                                                    (Prims.of_int (29))
                                                                    (Prims.of_int (497))
                                                                    (Prims.of_int (13)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    match uu___9
                                                                    with
                                                                    | 
                                                                    (pat1,
                                                                    subst1)
                                                                    ->
                                                                    let uu___10
                                                                    =
                                                                    deep_apply_subst
                                                                    e tm
                                                                    subst1 in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (496))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (496))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (497))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (497))
                                                                    (Prims.of_int (13)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun tm1
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (pat1,
                                                                    tm1)))))
                                                                    uu___9)))
                                                                uu___7))) in
                                             Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.InteractiveHelpers.Base.fst"
                                                           (Prims.of_int (493))
                                                           (Prims.of_int (43))
                                                           (Prims.of_int (497))
                                                           (Prims.of_int (13)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.InteractiveHelpers.Base.fst"
                                                           (Prims.of_int (498))
                                                           (Prims.of_int (6))
                                                           (Prims.of_int (500))
                                                           (Prims.of_int (46)))))
                                                  (Obj.magic uu___4)
                                                  (fun uu___5 ->
                                                     (fun
                                                        deep_apply_subst_in_branch
                                                        ->
                                                        let uu___5 =
                                                          FStar_Tactics_Util.map
                                                            deep_apply_subst_in_branch
                                                            branches in
                                                        Obj.magic
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (499))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (499))
                                                                    (Prims.of_int (58)))))
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (500))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (500))
                                                                    (Prims.of_int (46)))))
                                                             (Obj.magic
                                                                uu___5)
                                                             (fun uu___6 ->
                                                                (fun
                                                                   branches1
                                                                   ->
                                                                   Obj.magic
                                                                    (FStarC_Tactics_V1_Builtins.pack
                                                                    (FStarC_Reflection_V1_Data.Tv_Match
                                                                    (scrutinee1,
                                                                    ret_opt1,
                                                                    branches1))))
                                                                  uu___6)))
                                                       uu___5))) uu___4)))
                                 uu___3)))
                | FStarC_Reflection_V1_Data.Tv_AscribedT
                    (exp, ty, tac, use_eq) ->
                    Obj.magic
                      (Obj.repr
                         (let uu___2 = deep_apply_subst e exp subst in
                          FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.InteractiveHelpers.Base.fst"
                                     (Prims.of_int (502)) (Prims.of_int (14))
                                     (Prims.of_int (502)) (Prims.of_int (42)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.InteractiveHelpers.Base.fst"
                                     (Prims.of_int (502)) (Prims.of_int (45))
                                     (Prims.of_int (505)) (Prims.of_int (42)))))
                            (Obj.magic uu___2)
                            (fun uu___3 ->
                               (fun exp1 ->
                                  let uu___3 = deep_apply_subst e ty subst in
                                  Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.InteractiveHelpers.Base.fst"
                                                (Prims.of_int (503))
                                                (Prims.of_int (13))
                                                (Prims.of_int (503))
                                                (Prims.of_int (40)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.InteractiveHelpers.Base.fst"
                                                (Prims.of_int (505))
                                                (Prims.of_int (4))
                                                (Prims.of_int (505))
                                                (Prims.of_int (42)))))
                                       (Obj.magic uu___3)
                                       (fun uu___4 ->
                                          (fun ty1 ->
                                             Obj.magic
                                               (FStarC_Tactics_V1_Builtins.pack
                                                  (FStarC_Reflection_V1_Data.Tv_AscribedT
                                                     (exp1, ty1,
                                                       FStar_Pervasives_Native.None,
                                                       use_eq)))) uu___4)))
                                 uu___3)))
                | FStarC_Reflection_V1_Data.Tv_AscribedC
                    (exp, c, tac, use_eq) ->
                    Obj.magic
                      (Obj.repr
                         (let uu___2 = deep_apply_subst e exp subst in
                          FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.InteractiveHelpers.Base.fst"
                                     (Prims.of_int (507)) (Prims.of_int (14))
                                     (Prims.of_int (507)) (Prims.of_int (42)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.InteractiveHelpers.Base.fst"
                                     (Prims.of_int (507)) (Prims.of_int (45))
                                     (Prims.of_int (510)) (Prims.of_int (41)))))
                            (Obj.magic uu___2)
                            (fun uu___3 ->
                               (fun exp1 ->
                                  let uu___3 =
                                    deep_apply_subst_in_comp e c subst in
                                  Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.InteractiveHelpers.Base.fst"
                                                (Prims.of_int (508))
                                                (Prims.of_int (12))
                                                (Prims.of_int (508))
                                                (Prims.of_int (46)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.InteractiveHelpers.Base.fst"
                                                (Prims.of_int (510))
                                                (Prims.of_int (4))
                                                (Prims.of_int (510))
                                                (Prims.of_int (41)))))
                                       (Obj.magic uu___3)
                                       (fun uu___4 ->
                                          (fun c1 ->
                                             Obj.magic
                                               (FStarC_Tactics_V1_Builtins.pack
                                                  (FStarC_Reflection_V1_Data.Tv_AscribedC
                                                     (exp1, c1,
                                                       FStar_Pervasives_Native.None,
                                                       use_eq)))) uu___4)))
                                 uu___3)))
                | uu___2 ->
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_Effect.lift_div_tac (fun uu___3 -> t))))
               uu___1)
and (deep_apply_subst_in_bv :
  FStarC_Reflection_Types.env ->
    FStarC_Reflection_Types.bv ->
      (FStarC_Reflection_Types.bv * FStarC_Reflection_Types.term) Prims.list
        ->
        ((FStarC_Reflection_Types.bv * (FStarC_Reflection_Types.bv *
           FStarC_Reflection_Types.term) Prims.list),
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun e ->
    fun bv ->
      fun subst ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              FStarC_Tactics_V1_Builtins.pack
                (FStarC_Reflection_V1_Data.Tv_Var bv) in
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "FStar.InteractiveHelpers.Base.fst"
                       (Prims.of_int (518)) (Prims.of_int (11))
                       (Prims.of_int (518)) (Prims.of_int (27)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "FStar.InteractiveHelpers.Base.fst"
                       (Prims.of_int (518)) (Prims.of_int (6))
                       (Prims.of_int (518)) (Prims.of_int (28)))))
              (Obj.magic uu___2)
              (fun uu___3 ->
                 FStar_Tactics_Effect.lift_div_tac
                   (fun uu___4 -> (bv, uu___3))) in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.InteractiveHelpers.Base.fst"
                     (Prims.of_int (518)) (Prims.of_int (6))
                     (Prims.of_int (518)) (Prims.of_int (28)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.InteractiveHelpers.Base.fst"
                     (Prims.of_int (518)) (Prims.of_int (6))
                     (Prims.of_int (518)) (Prims.of_int (35)))))
            (Obj.magic uu___1)
            (fun uu___2 ->
               FStar_Tactics_Effect.lift_div_tac
                 (fun uu___3 -> uu___2 :: subst)) in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.InteractiveHelpers.Base.fst"
                   (Prims.of_int (518)) (Prims.of_int (6))
                   (Prims.of_int (518)) (Prims.of_int (35)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.InteractiveHelpers.Base.fst"
                   (Prims.of_int (518)) (Prims.of_int (2))
                   (Prims.of_int (518)) (Prims.of_int (35)))))
          (Obj.magic uu___)
          (fun uu___1 ->
             FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> (bv, uu___1)))
and (deep_apply_subst_in_binder :
  FStarC_Reflection_Types.env ->
    FStarC_Reflection_Types.binder ->
      (FStarC_Reflection_Types.bv * FStarC_Reflection_Types.term) Prims.list
        ->
        ((FStarC_Reflection_Types.binder * (FStarC_Reflection_Types.bv *
           FStarC_Reflection_Types.term) Prims.list),
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun e ->
    fun br ->
      fun subst ->
        match FStarC_Reflection_V1_Builtins.inspect_binder br with
        | { FStarC_Reflection_V1_Data.binder_bv = binder_bv;
            FStarC_Reflection_V1_Data.binder_qual = binder_qual;
            FStarC_Reflection_V1_Data.binder_attrs = binder_attrs;
            FStarC_Reflection_V1_Data.binder_sort = binder_sort;_} ->
            let uu___ = deep_apply_subst e binder_sort subst in
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "FStar.InteractiveHelpers.Base.fst"
                       (Prims.of_int (525)) (Prims.of_int (20))
                       (Prims.of_int (525)) (Prims.of_int (56)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "FStar.InteractiveHelpers.Base.fst"
                       (Prims.of_int (525)) (Prims.of_int (59))
                       (Prims.of_int (532)) (Prims.of_int (10)))))
              (Obj.magic uu___)
              (fun uu___1 ->
                 (fun binder_sort1 ->
                    let uu___1 = deep_apply_subst_in_bv e binder_bv subst in
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.InteractiveHelpers.Base.fst"
                                  (Prims.of_int (526)) (Prims.of_int (25))
                                  (Prims.of_int (526)) (Prims.of_int (65)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.InteractiveHelpers.Base.fst"
                                  (Prims.of_int (525)) (Prims.of_int (59))
                                  (Prims.of_int (532)) (Prims.of_int (10)))))
                         (Obj.magic uu___1)
                         (fun uu___2 ->
                            FStar_Tactics_Effect.lift_div_tac
                              (fun uu___3 ->
                                 match uu___2 with
                                 | (binder_bv1, subst1) ->
                                     ((FStarC_Reflection_V1_Builtins.pack_binder
                                         {
                                           FStarC_Reflection_V1_Data.binder_bv
                                             = binder_bv1;
                                           FStarC_Reflection_V1_Data.binder_qual
                                             = binder_qual;
                                           FStarC_Reflection_V1_Data.binder_attrs
                                             = binder_attrs;
                                           FStarC_Reflection_V1_Data.binder_sort
                                             = binder_sort1
                                         }), subst1))))) uu___1)
and (deep_apply_subst_in_comp :
  FStarC_Reflection_Types.env ->
    FStarC_Reflection_Types.comp ->
      (FStarC_Reflection_Types.bv * FStarC_Reflection_Types.term) Prims.list
        -> (FStarC_Reflection_Types.comp, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun e ->
    fun c ->
      fun subst ->
        let uu___ =
          Obj.magic
            (FStar_Tactics_Effect.lift_div_tac
               (fun uu___1 -> fun x -> deep_apply_subst e x subst)) in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.InteractiveHelpers.Base.fst"
                   (Prims.of_int (535)) (Prims.of_int (14))
                   (Prims.of_int (535)) (Prims.of_int (51)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.InteractiveHelpers.Base.fst"
                   (Prims.of_int (535)) (Prims.of_int (54))
                   (Prims.of_int (558)) (Prims.of_int (55)))))
          (Obj.magic uu___)
          (fun uu___1 ->
             (fun subst1 ->
                let uu___1 =
                  Obj.magic
                    (FStar_Tactics_Effect.lift_div_tac
                       (fun uu___3 ->
                          fun uu___2 ->
                            (fun uu___2 ->
                               fun a ->
                                 match a with
                                 | FStarC_Reflection_V1_Data.Q_Implicit ->
                                     Obj.magic
                                       (Obj.repr
                                          (FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___3 -> a)))
                                 | FStarC_Reflection_V1_Data.Q_Explicit ->
                                     Obj.magic
                                       (Obj.repr
                                          (FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___3 -> a)))
                                 | FStarC_Reflection_V1_Data.Q_Meta t ->
                                     Obj.magic
                                       (Obj.repr
                                          (let uu___3 = subst1 t in
                                           FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "FStar.InteractiveHelpers.Base.fst"
                                                      (Prims.of_int (540))
                                                      (Prims.of_int (25))
                                                      (Prims.of_int (540))
                                                      (Prims.of_int (34)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "FStar.InteractiveHelpers.Base.fst"
                                                      (Prims.of_int (540))
                                                      (Prims.of_int (18))
                                                      (Prims.of_int (540))
                                                      (Prims.of_int (34)))))
                                             (Obj.magic uu___3)
                                             (fun uu___4 ->
                                                FStar_Tactics_Effect.lift_div_tac
                                                  (fun uu___5 ->
                                                     FStarC_Reflection_V1_Data.Q_Meta
                                                       uu___4))))) uu___3
                              uu___2)) in
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.InteractiveHelpers.Base.fst"
                              (Prims.of_int (537)) (Prims.of_int (4))
                              (Prims.of_int (540)) (Prims.of_int (34)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.InteractiveHelpers.Base.fst"
                              (Prims.of_int (542)) (Prims.of_int (2))
                              (Prims.of_int (558)) (Prims.of_int (55)))))
                     (Obj.magic uu___1)
                     (fun uu___2 ->
                        (fun subst_in_aqualv ->
                           match FStarC_Reflection_V1_Builtins.inspect_comp c
                           with
                           | FStarC_Reflection_V1_Data.C_Total ret ->
                               let uu___2 = subst1 ret in
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.InteractiveHelpers.Base.fst"
                                             (Prims.of_int (544))
                                             (Prims.of_int (14))
                                             (Prims.of_int (544))
                                             (Prims.of_int (23)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.InteractiveHelpers.Base.fst"
                                             (Prims.of_int (545))
                                             (Prims.of_int (4))
                                             (Prims.of_int (545))
                                             (Prims.of_int (27)))))
                                    (Obj.magic uu___2)
                                    (fun ret1 ->
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___3 ->
                                            FStarC_Reflection_V1_Builtins.pack_comp
                                              (FStarC_Reflection_V1_Data.C_Total
                                                 ret1))))
                           | FStarC_Reflection_V1_Data.C_GTotal ret ->
                               let uu___2 = subst1 ret in
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.InteractiveHelpers.Base.fst"
                                             (Prims.of_int (547))
                                             (Prims.of_int (14))
                                             (Prims.of_int (547))
                                             (Prims.of_int (23)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.InteractiveHelpers.Base.fst"
                                             (Prims.of_int (548))
                                             (Prims.of_int (4))
                                             (Prims.of_int (548))
                                             (Prims.of_int (28)))))
                                    (Obj.magic uu___2)
                                    (fun ret1 ->
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___3 ->
                                            FStarC_Reflection_V1_Builtins.pack_comp
                                              (FStarC_Reflection_V1_Data.C_GTotal
                                                 ret1))))
                           | FStarC_Reflection_V1_Data.C_Lemma
                               (pre, post, patterns) ->
                               let uu___2 = subst1 pre in
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.InteractiveHelpers.Base.fst"
                                             (Prims.of_int (550))
                                             (Prims.of_int (14))
                                             (Prims.of_int (550))
                                             (Prims.of_int (23)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.InteractiveHelpers.Base.fst"
                                             (Prims.of_int (550))
                                             (Prims.of_int (26))
                                             (Prims.of_int (553))
                                             (Prims.of_int (41)))))
                                    (Obj.magic uu___2)
                                    (fun uu___3 ->
                                       (fun pre1 ->
                                          let uu___3 = subst1 post in
                                          Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "FStar.InteractiveHelpers.Base.fst"
                                                        (Prims.of_int (551))
                                                        (Prims.of_int (15))
                                                        (Prims.of_int (551))
                                                        (Prims.of_int (25)))))
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "FStar.InteractiveHelpers.Base.fst"
                                                        (Prims.of_int (551))
                                                        (Prims.of_int (28))
                                                        (Prims.of_int (553))
                                                        (Prims.of_int (41)))))
                                               (Obj.magic uu___3)
                                               (fun uu___4 ->
                                                  (fun post1 ->
                                                     let uu___4 =
                                                       subst1 patterns in
                                                     Obj.magic
                                                       (FStar_Tactics_Effect.tac_bind
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "FStar.InteractiveHelpers.Base.fst"
                                                                   (Prims.of_int (552))
                                                                   (Prims.of_int (19))
                                                                   (Prims.of_int (552))
                                                                   (Prims.of_int (33)))))
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "FStar.InteractiveHelpers.Base.fst"
                                                                   (Prims.of_int (553))
                                                                   (Prims.of_int (4))
                                                                   (Prims.of_int (553))
                                                                   (Prims.of_int (41)))))
                                                          (Obj.magic uu___4)
                                                          (fun patterns1 ->
                                                             FStar_Tactics_Effect.lift_div_tac
                                                               (fun uu___5 ->
                                                                  FStarC_Reflection_V1_Builtins.pack_comp
                                                                    (
                                                                    FStarC_Reflection_V1_Data.C_Lemma
                                                                    (pre1,
                                                                    post1,
                                                                    patterns1))))))
                                                    uu___4))) uu___3))
                           | FStarC_Reflection_V1_Data.C_Eff
                               (us, eff_name, result, eff_args, decrs) ->
                               let uu___2 = subst1 result in
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.InteractiveHelpers.Base.fst"
                                             (Prims.of_int (555))
                                             (Prims.of_int (17))
                                             (Prims.of_int (555))
                                             (Prims.of_int (29)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.InteractiveHelpers.Base.fst"
                                             (Prims.of_int (555))
                                             (Prims.of_int (32))
                                             (Prims.of_int (558))
                                             (Prims.of_int (55)))))
                                    (Obj.magic uu___2)
                                    (fun uu___3 ->
                                       (fun result1 ->
                                          let uu___3 =
                                            FStar_Tactics_Util.map
                                              (fun uu___4 ->
                                                 match uu___4 with
                                                 | (x, a) ->
                                                     let uu___5 = subst1 x in
                                                     FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "FStar.InteractiveHelpers.Base.fst"
                                                                (Prims.of_int (556))
                                                                (Prims.of_int (39))
                                                                (Prims.of_int (556))
                                                                (Prims.of_int (46)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "FStar.InteractiveHelpers.Base.fst"
                                                                (Prims.of_int (556))
                                                                (Prims.of_int (38))
                                                                (Prims.of_int (556))
                                                                (Prims.of_int (66)))))
                                                       (Obj.magic uu___5)
                                                       (fun uu___6 ->
                                                          (fun uu___6 ->
                                                             let uu___7 =
                                                               subst_in_aqualv
                                                                 a in
                                                             Obj.magic
                                                               (FStar_Tactics_Effect.tac_bind
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (556))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (556))
                                                                    (Prims.of_int (65)))))
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (556))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (556))
                                                                    (Prims.of_int (66)))))
                                                                  (Obj.magic
                                                                    uu___7)
                                                                  (fun uu___8
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    (uu___6,
                                                                    uu___8)))))
                                                            uu___6)) eff_args in
                                          Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "FStar.InteractiveHelpers.Base.fst"
                                                        (Prims.of_int (556))
                                                        (Prims.of_int (19))
                                                        (Prims.of_int (556))
                                                        (Prims.of_int (76)))))
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "FStar.InteractiveHelpers.Base.fst"
                                                        (Prims.of_int (556))
                                                        (Prims.of_int (79))
                                                        (Prims.of_int (558))
                                                        (Prims.of_int (55)))))
                                               (Obj.magic uu___3)
                                               (fun uu___4 ->
                                                  (fun eff_args1 ->
                                                     let uu___4 =
                                                       FStar_Tactics_Util.map
                                                         subst1 decrs in
                                                     Obj.magic
                                                       (FStar_Tactics_Effect.tac_bind
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "FStar.InteractiveHelpers.Base.fst"
                                                                   (Prims.of_int (557))
                                                                   (Prims.of_int (16))
                                                                   (Prims.of_int (557))
                                                                   (Prims.of_int (31)))))
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "FStar.InteractiveHelpers.Base.fst"
                                                                   (Prims.of_int (558))
                                                                   (Prims.of_int (4))
                                                                   (Prims.of_int (558))
                                                                   (Prims.of_int (55)))))
                                                          (Obj.magic uu___4)
                                                          (fun decrs1 ->
                                                             FStar_Tactics_Effect.lift_div_tac
                                                               (fun uu___5 ->
                                                                  FStarC_Reflection_V1_Builtins.pack_comp
                                                                    (
                                                                    FStarC_Reflection_V1_Data.C_Eff
                                                                    (us,
                                                                    eff_name,
                                                                    result1,
                                                                    eff_args1,
                                                                    decrs1))))))
                                                    uu___4))) uu___3)))
                          uu___2))) uu___1)
and (deep_apply_subst_in_pattern :
  FStarC_Reflection_Types.env ->
    FStarC_Reflection_V1_Data.pattern ->
      (FStarC_Reflection_Types.bv * FStarC_Reflection_Types.term) Prims.list
        ->
        ((FStarC_Reflection_V1_Data.pattern * (FStarC_Reflection_Types.bv *
           FStarC_Reflection_Types.term) Prims.list),
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun e ->
           fun pat ->
             fun subst ->
               match pat with
               | FStarC_Reflection_V1_Data.Pat_Constant uu___ ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.lift_div_tac
                           (fun uu___1 -> (pat, subst))))
               | FStarC_Reflection_V1_Data.Pat_Cons (fv, us, patterns) ->
                   Obj.magic
                     (Obj.repr
                        (let uu___ =
                           FStar_Tactics_Util.fold_right
                             (fun uu___1 ->
                                fun uu___2 ->
                                  match (uu___1, uu___2) with
                                  | ((pat1, b), (pats, subst1)) ->
                                      let uu___3 =
                                        deep_apply_subst_in_pattern e pat1
                                          subst1 in
                                      FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "FStar.InteractiveHelpers.Base.fst"
                                                 (Prims.of_int (568))
                                                 (Prims.of_int (39))
                                                 (Prims.of_int (568))
                                                 (Prims.of_int (78)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "FStar.InteractiveHelpers.Base.fst"
                                                 (Prims.of_int (567))
                                                 (Prims.of_int (47))
                                                 (Prims.of_int (569))
                                                 (Prims.of_int (47)))))
                                        (Obj.magic uu___3)
                                        (fun uu___4 ->
                                           FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___5 ->
                                                match uu___4 with
                                                | (pat2, subst2) ->
                                                    (((pat2, b) :: pats),
                                                      subst2)))) patterns
                             ([], subst) in
                         FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "FStar.InteractiveHelpers.Base.fst"
                                    (Prims.of_int (567)) (Prims.of_int (6))
                                    (Prims.of_int (569)) (Prims.of_int (69)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "FStar.InteractiveHelpers.Base.fst"
                                    (Prims.of_int (563)) (Prims.of_int (30))
                                    (Prims.of_int (571)) (Prims.of_int (34)))))
                           (Obj.magic uu___)
                           (fun uu___1 ->
                              FStar_Tactics_Effect.lift_div_tac
                                (fun uu___2 ->
                                   match uu___1 with
                                   | (patterns1, subst1) ->
                                       ((FStarC_Reflection_V1_Data.Pat_Cons
                                           (fv, us, patterns1)), subst1)))))
               | FStarC_Reflection_V1_Data.Pat_Var (bv, st) ->
                   Obj.magic
                     (Obj.repr
                        (let uu___ =
                           let uu___1 =
                             let uu___2 = FStarC_Tactics_Unseal.unseal st in
                             FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "FStar.InteractiveHelpers.Base.fst"
                                        (Prims.of_int (573))
                                        (Prims.of_int (45))
                                        (Prims.of_int (573))
                                        (Prims.of_int (56)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "FStar.InteractiveHelpers.Base.fst"
                                        (Prims.of_int (573))
                                        (Prims.of_int (25))
                                        (Prims.of_int (573))
                                        (Prims.of_int (63)))))
                               (Obj.magic uu___2)
                               (fun uu___3 ->
                                  (fun uu___3 ->
                                     Obj.magic
                                       (deep_apply_subst e uu___3 subst))
                                    uu___3) in
                           FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "FStar.InteractiveHelpers.Base.fst"
                                      (Prims.of_int (573))
                                      (Prims.of_int (25))
                                      (Prims.of_int (573))
                                      (Prims.of_int (63)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "FStar.InteractiveHelpers.Base.fst"
                                      (Prims.of_int (573))
                                      (Prims.of_int (13))
                                      (Prims.of_int (573))
                                      (Prims.of_int (63)))))
                             (Obj.magic uu___1)
                             (fun uu___2 ->
                                FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___3 -> FStar_Sealed.seal uu___2)) in
                         FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "FStar.InteractiveHelpers.Base.fst"
                                    (Prims.of_int (573)) (Prims.of_int (13))
                                    (Prims.of_int (573)) (Prims.of_int (63)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "FStar.InteractiveHelpers.Base.fst"
                                    (Prims.of_int (573)) (Prims.of_int (66))
                                    (Prims.of_int (575)) (Prims.of_int (24)))))
                           (Obj.magic uu___)
                           (fun uu___1 ->
                              (fun st1 ->
                                 let uu___1 =
                                   deep_apply_subst_in_bv e bv subst in
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "FStar.InteractiveHelpers.Base.fst"
                                               (Prims.of_int (574))
                                               (Prims.of_int (20))
                                               (Prims.of_int (574))
                                               (Prims.of_int (53)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "FStar.InteractiveHelpers.Base.fst"
                                               (Prims.of_int (573))
                                               (Prims.of_int (66))
                                               (Prims.of_int (575))
                                               (Prims.of_int (24)))))
                                      (Obj.magic uu___1)
                                      (fun uu___2 ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___3 ->
                                              match uu___2 with
                                              | (bv1, subst1) ->
                                                  ((FStarC_Reflection_V1_Data.Pat_Var
                                                      (bv1, st1)), subst1)))))
                                uu___1)))
               | FStarC_Reflection_V1_Data.Pat_Dot_Term eopt ->
                   Obj.magic
                     (Obj.repr
                        (let uu___ =
                           let uu___1 =
                             FStar_Tactics_Util.map_opt
                               (fun t -> deep_apply_subst e t subst) eopt in
                           FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "FStar.InteractiveHelpers.Base.fst"
                                      (Prims.of_int (577))
                                      (Prims.of_int (17))
                                      (Prims.of_int (577))
                                      (Prims.of_int (69)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "FStar.InteractiveHelpers.Base.fst"
                                      (Prims.of_int (577)) (Prims.of_int (4))
                                      (Prims.of_int (577))
                                      (Prims.of_int (69)))))
                             (Obj.magic uu___1)
                             (fun uu___2 ->
                                FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___3 ->
                                     FStarC_Reflection_V1_Data.Pat_Dot_Term
                                       uu___2)) in
                         FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "FStar.InteractiveHelpers.Base.fst"
                                    (Prims.of_int (577)) (Prims.of_int (4))
                                    (Prims.of_int (577)) (Prims.of_int (69)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "FStar.InteractiveHelpers.Base.fst"
                                    (Prims.of_int (577)) (Prims.of_int (4))
                                    (Prims.of_int (577)) (Prims.of_int (76)))))
                           (Obj.magic uu___)
                           (fun uu___1 ->
                              FStar_Tactics_Effect.lift_div_tac
                                (fun uu___2 -> (uu___1, subst)))))) uu___2
          uu___1 uu___
let (apply_subst :
  FStarC_Reflection_Types.env ->
    FStarC_Reflection_Types.term ->
      ((FStarC_Reflection_Types.bv * FStarC_Reflection_Types.typ) *
        FStarC_Reflection_Types.term) Prims.list ->
        (FStarC_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
  = norm_apply_subst
let (apply_subst_in_comp :
  FStarC_Reflection_Types.env ->
    FStarC_Reflection_Types.comp ->
      ((FStarC_Reflection_Types.bv * FStarC_Reflection_Types.typ) *
        FStarC_Reflection_Types.term) Prims.list ->
        (FStarC_Reflection_Types.comp, unit) FStar_Tactics_Effect.tac_repr)
  = norm_apply_subst_in_comp
let (opt_apply_subst :
  FStarC_Reflection_Types.env ->
    FStarC_Reflection_Types.term FStar_Pervasives_Native.option ->
      ((FStarC_Reflection_Types.bv * FStarC_Reflection_Types.typ) *
        FStarC_Reflection_Types.term) Prims.list ->
        (FStarC_Reflection_Types.term FStar_Pervasives_Native.option, 
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun e ->
           fun opt_t ->
             fun subst ->
               match opt_t with
               | FStar_Pervasives_Native.None ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.lift_div_tac
                           (fun uu___ -> FStar_Pervasives_Native.None)))
               | FStar_Pervasives_Native.Some t ->
                   Obj.magic
                     (Obj.repr
                        (let uu___ = apply_subst e t subst in
                         FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "FStar.InteractiveHelpers.Base.fst"
                                    (Prims.of_int (593)) (Prims.of_int (19))
                                    (Prims.of_int (593)) (Prims.of_int (42)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "FStar.InteractiveHelpers.Base.fst"
                                    (Prims.of_int (593)) (Prims.of_int (14))
                                    (Prims.of_int (593)) (Prims.of_int (42)))))
                           (Obj.magic uu___)
                           (fun uu___1 ->
                              FStar_Tactics_Effect.lift_div_tac
                                (fun uu___2 ->
                                   FStar_Pervasives_Native.Some uu___1)))))
          uu___2 uu___1 uu___
let rec (_generate_shadowed_subst :
  genv ->
    FStarC_Reflection_Types.term ->
      (FStarC_Reflection_Types.bv * FStarC_Reflection_Types.typ) Prims.list
        ->
        ((genv * (FStarC_Reflection_Types.bv * FStarC_Reflection_Types.typ *
           FStarC_Reflection_Types.bv) Prims.list),
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun ge ->
           fun t ->
             fun bvl ->
               match bvl with
               | [] ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.lift_div_tac
                           (fun uu___ -> (ge, []))))
               | old_bv::bvl' ->
                   Obj.magic
                     (Obj.repr
                        (let uu___ = FStarC_Tactics_V1_Builtins.inspect t in
                         FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "FStar.InteractiveHelpers.Base.fst"
                                    (Prims.of_int (612)) (Prims.of_int (10))
                                    (Prims.of_int (612)) (Prims.of_int (19)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "FStar.InteractiveHelpers.Base.fst"
                                    (Prims.of_int (612)) (Prims.of_int (4))
                                    (Prims.of_int (626)) (Prims.of_int (55)))))
                           (Obj.magic uu___)
                           (fun uu___1 ->
                              (fun uu___1 ->
                                 match uu___1 with
                                 | FStarC_Reflection_V1_Data.Tv_Abs
                                     (b, uu___2) ->
                                     let uu___3 =
                                       Obj.magic
                                         (FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___4 ->
                                               (FStarC_Reflection_V1_Builtins.inspect_binder
                                                  b).FStarC_Reflection_V1_Data.binder_bv)) in
                                     Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "FStar.InteractiveHelpers.Base.fst"
                                                   (Prims.of_int (615))
                                                   (Prims.of_int (15))
                                                   (Prims.of_int (615))
                                                   (Prims.of_int (43)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "FStar.InteractiveHelpers.Base.fst"
                                                   (Prims.of_int (615))
                                                   (Prims.of_int (46))
                                                   (Prims.of_int (625))
                                                   (Prims.of_int (42)))))
                                          (Obj.magic uu___3)
                                          (fun uu___4 ->
                                             (fun bv ->
                                                let uu___4 =
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___5 ->
                                                          FStarC_Reflection_V1_Builtins.inspect_bv
                                                            bv)) in
                                                Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "FStar.InteractiveHelpers.Base.fst"
                                                              (Prims.of_int (616))
                                                              (Prims.of_int (16))
                                                              (Prims.of_int (616))
                                                              (Prims.of_int (29)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "FStar.InteractiveHelpers.Base.fst"
                                                              (Prims.of_int (616))
                                                              (Prims.of_int (32))
                                                              (Prims.of_int (625))
                                                              (Prims.of_int (42)))))
                                                     (Obj.magic uu___4)
                                                     (fun uu___5 ->
                                                        (fun bvv ->
                                                           let uu___5 =
                                                             FStar_Tactics_V1_Derived.binder_sort
                                                               b in
                                                           Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (617))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (617))
                                                                    (Prims.of_int (28)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (617))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (625))
                                                                    (Prims.of_int (42)))))
                                                                (Obj.magic
                                                                   uu___5)
                                                                (fun uu___6
                                                                   ->
                                                                   (fun ty ->
                                                                    let uu___6
                                                                    =
                                                                    FStarC_Tactics_Unseal.unseal
                                                                    bvv.FStarC_Reflection_V1_Data.bv_ppname in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (618))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (618))
                                                                    (Prims.of_int (37)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (618))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (625))
                                                                    (Prims.of_int (42)))))
                                                                    (Obj.magic
                                                                    uu___6)
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun name
                                                                    ->
                                                                    let uu___7
                                                                    =
                                                                    genv_push_fresh_bv
                                                                    ge
                                                                    (Prims.strcat
                                                                    "__" name)
                                                                    ty in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (619))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (619))
                                                                    (Prims.of_int (61)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (618))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (625))
                                                                    (Prims.of_int (42)))))
                                                                    (Obj.magic
                                                                    uu___7)
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    match uu___8
                                                                    with
                                                                    | 
                                                                    (ge1,
                                                                    fresh) ->
                                                                    let uu___9
                                                                    =
                                                                    let uu___10
                                                                    =
                                                                    let uu___11
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.pack
                                                                    (FStarC_Reflection_V1_Data.Tv_Var
                                                                    fresh) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (620))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (620))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (620))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (620))
                                                                    (Prims.of_int (47)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    [uu___12])) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (620))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (620))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (620))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (620))
                                                                    (Prims.of_int (47)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_Reflection_V1_Derived.mk_e_app
                                                                    t uu___11)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (620))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (620))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (620))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (625))
                                                                    (Prims.of_int (42)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun t1
                                                                    ->
                                                                    let uu___10
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.norm_term_env
                                                                    ge1.env
                                                                    [] t1 in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (621))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (621))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (621))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (625))
                                                                    (Prims.of_int (42)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun t2
                                                                    ->
                                                                    let uu___11
                                                                    =
                                                                    _generate_shadowed_subst
                                                                    ge1 t2
                                                                    bvl' in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (623))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (623))
                                                                    (Prims.of_int (58)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Base.fst"
                                                                    (Prims.of_int (621))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (625))
                                                                    (Prims.of_int (42)))))
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
                                                                    (ge2,
                                                                    nbvl) ->
                                                                    (ge2,
                                                                    (((FStar_Pervasives_Native.fst
                                                                    old_bv),
                                                                    ty,
                                                                    fresh) ::
                                                                    nbvl))))))
                                                                    uu___11)))
                                                                    uu___10)))
                                                                    uu___8)))
                                                                    uu___7)))
                                                                    uu___6)))
                                                          uu___5))) uu___4))
                                 | uu___2 ->
                                     Obj.magic
                                       (mfail
                                          "_subst_with_fresh_vars: not a Tv_Abs"))
                                uu___1)))) uu___2 uu___1 uu___
let (generate_shadowed_subst :
  genv ->
    ((genv * (FStarC_Reflection_Types.bv * FStarC_Reflection_Types.typ *
       FStarC_Reflection_Types.bv) Prims.list),
      unit) FStar_Tactics_Effect.tac_repr)
  =
  fun ge ->
    let uu___ =
      Obj.magic
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___1 -> FStar_List_Tot_Base.rev ge.svars)) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.InteractiveHelpers.Base.fst"
               (Prims.of_int (630)) (Prims.of_int (12)) (Prims.of_int (630))
               (Prims.of_int (33)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.InteractiveHelpers.Base.fst"
               (Prims.of_int (630)) (Prims.of_int (36)) (Prims.of_int (633))
               (Prims.of_int (39))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun bvl ->
            let uu___1 =
              Obj.magic
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___2 ->
                      FStar_List_Tot_Base.map
                        (fun uu___3 ->
                           match uu___3 with
                           | (bv, sort) ->
                               FStar_Reflection_V1_Derived.mk_binder bv sort)
                        bvl)) in
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range
                          "FStar.InteractiveHelpers.Base.fst"
                          (Prims.of_int (631)) (Prims.of_int (11))
                          (Prims.of_int (631)) (Prims.of_int (65)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range
                          "FStar.InteractiveHelpers.Base.fst"
                          (Prims.of_int (631)) (Prims.of_int (68))
                          (Prims.of_int (633)) (Prims.of_int (39)))))
                 (Obj.magic uu___1)
                 (fun uu___2 ->
                    (fun bl ->
                       let uu___2 =
                         FStar_Tactics_V1_Derived.mk_abs bl
                           (FStarC_Reflection_V2_Builtins.pack_ln
                              (FStarC_Reflection_V2_Data.Tv_Const
                                 FStarC_Reflection_V2_Data.C_Unit)) in
                       Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.InteractiveHelpers.Base.fst"
                                     (Prims.of_int (632)) (Prims.of_int (14))
                                     (Prims.of_int (632)) (Prims.of_int (29)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.InteractiveHelpers.Base.fst"
                                     (Prims.of_int (633)) (Prims.of_int (2))
                                     (Prims.of_int (633)) (Prims.of_int (39)))))
                            (Obj.magic uu___2)
                            (fun uu___3 ->
                               (fun dummy ->
                                  Obj.magic
                                    (_generate_shadowed_subst ge dummy bvl))
                                 uu___3))) uu___2))) uu___1)