open Prims
let (term_eq :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term ->
      (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  = FStar_Tactics_Builtins.term_eq_old
type proposition = FStar_Reflection_Types.term
let (proposition_to_string :
  proposition -> (Prims.string, unit) FStar_Tactics_Effect.tac_repr) =
  fun p -> FStar_Tactics_Builtins.term_to_string p
type assertions =
  {
  pres: proposition Prims.list ;
  posts: proposition Prims.list }
let (__proj__Mkassertions__item__pres : assertions -> proposition Prims.list)
  = fun projectee -> match projectee with | { pres; posts;_} -> pres
let (__proj__Mkassertions__item__posts :
  assertions -> proposition Prims.list) =
  fun projectee -> match projectee with | { pres; posts;_} -> posts
let (mk_assertions :
  proposition Prims.list -> proposition Prims.list -> assertions) =
  fun pres -> fun posts -> { pres; posts }
let (simpl_norm_steps : FStar_Pervasives.norm_step Prims.list) =
  [FStar_Pervasives.primops;
  FStar_Pervasives.simplify;
  FStar_Pervasives.iota]
let (is_trivial_proposition :
  proposition -> (Prims.bool, unit) FStar_Tactics_Effect.tac_repr) =
  fun p ->
    term_eq
      (FStar_Reflection_Builtins.pack_ln
         (FStar_Reflection_Data.Tv_FVar
            (FStar_Reflection_Builtins.pack_fv ["Prims"; "l_True"]))) p
let (simp_filter_proposition :
  FStar_Reflection_Types.env ->
    FStar_Pervasives.norm_step Prims.list ->
      proposition ->
        (proposition Prims.list, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun e ->
    fun steps ->
      fun p ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Range.mk_range "FStar.InteractiveHelpers.Propositions.fst"
             (Prims.of_int (52)) (Prims.of_int (14)) (Prims.of_int (52))
             (Prims.of_int (37)))
          (FStar_Range.mk_range "FStar.InteractiveHelpers.Propositions.fst"
             (Prims.of_int (54)) (Prims.of_int (2)) (Prims.of_int (55))
             (Prims.of_int (14)))
          (Obj.magic (FStar_Tactics_Builtins.norm_term_env e steps p))
          (fun uu___ ->
             (fun prop1 ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Range.mk_range
                        "FStar.InteractiveHelpers.Propositions.fst"
                        (Prims.of_int (54)) (Prims.of_int (5))
                        (Prims.of_int (54)) (Prims.of_int (34)))
                     (FStar_Range.mk_range
                        "FStar.InteractiveHelpers.Propositions.fst"
                        (Prims.of_int (54)) (Prims.of_int (2))
                        (Prims.of_int (55)) (Prims.of_int (14)))
                     (Obj.magic
                        (term_eq
                           (FStar_Reflection_Builtins.pack_ln
                              (FStar_Reflection_Data.Tv_FVar
                                 (FStar_Reflection_Builtins.pack_fv
                                    ["Prims"; "l_True"]))) prop1))
                     (fun uu___ ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___1 -> if uu___ then [] else [prop1]))))
               uu___)
let (simp_filter_propositions :
  FStar_Reflection_Types.env ->
    FStar_Pervasives.norm_step Prims.list ->
      proposition Prims.list ->
        (proposition Prims.list, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun e ->
    fun steps ->
      fun pl ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Range.mk_range "FStar.InteractiveHelpers.Propositions.fst"
             (Prims.of_int (59)) (Prims.of_int (15)) (Prims.of_int (59))
             (Prims.of_int (57)))
          (FStar_Range.mk_range "FStar.InteractiveHelpers.Propositions.fst"
             (Prims.of_int (59)) (Prims.of_int (2)) (Prims.of_int (59))
             (Prims.of_int (57)))
          (Obj.magic
             (FStar_Tactics_Util.map (simp_filter_proposition e steps) pl))
          (fun uu___ ->
             FStar_Tactics_Effect.lift_div_tac
               (fun uu___1 -> FStar_List_Tot_Base.flatten uu___))
let (simp_filter_assertions :
  FStar_Reflection_Types.env ->
    FStar_Pervasives.norm_step Prims.list ->
      assertions -> (assertions, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun e ->
    fun steps ->
      fun a ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Range.mk_range "FStar.InteractiveHelpers.Propositions.fst"
             (Prims.of_int (63)) (Prims.of_int (13)) (Prims.of_int (63))
             (Prims.of_int (52)))
          (FStar_Range.mk_range "FStar.InteractiveHelpers.Propositions.fst"
             (Prims.of_int (63)) (Prims.of_int (55)) (Prims.of_int (64))
             (Prims.of_int (57)))
          (Obj.magic (simp_filter_propositions e steps a.pres))
          (fun uu___ ->
             (fun pres ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Range.mk_range
                        "FStar.InteractiveHelpers.Propositions.fst"
                        (Prims.of_int (64)) (Prims.of_int (14))
                        (Prims.of_int (64)) (Prims.of_int (54)))
                     (FStar_Range.mk_range
                        "FStar.InteractiveHelpers.Propositions.fst"
                        (Prims.of_int (65)) (Prims.of_int (2))
                        (Prims.of_int (65)) (Prims.of_int (26)))
                     (Obj.magic (simp_filter_propositions e steps a.posts))
                     (fun posts ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___ -> mk_assertions pres posts)))) uu___)