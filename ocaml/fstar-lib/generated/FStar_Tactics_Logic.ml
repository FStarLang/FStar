open Prims
let (cur_formula :
  unit ->
    (FStar_Reflection_Formula.formula, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Range.mk_range "FStar.Tactics.Logic.fst" (Prims.of_int (26))
         (Prims.of_int (51)) (Prims.of_int (26)) (Prims.of_int (64)))
      (FStar_Range.mk_range "FStar.Tactics.Logic.fst" (Prims.of_int (26))
         (Prims.of_int (35)) (Prims.of_int (26)) (Prims.of_int (64)))
      (Obj.magic (FStar_Tactics_Derived.cur_goal ()))
      (fun uu___1 ->
         (fun uu___1 ->
            Obj.magic (FStar_Reflection_Formula.term_as_formula uu___1))
           uu___1)
let (l_revert : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Range.mk_range "FStar.Tactics.Logic.fst" (Prims.of_int (35))
         (Prims.of_int (4)) (Prims.of_int (35)) (Prims.of_int (13)))
      (FStar_Range.mk_range "FStar.Tactics.Logic.fst" (Prims.of_int (36))
         (Prims.of_int (4)) (Prims.of_int (36)) (Prims.of_int (26)))
      (Obj.magic (FStar_Tactics_Builtins.revert ()))
      (fun uu___1 ->
         (fun uu___1 ->
            Obj.magic
              (FStar_Tactics_Derived.apply
                 (FStar_Reflection_Builtins.pack_ln
                    (FStar_Reflection_Data.Tv_FVar
                       (FStar_Reflection_Builtins.pack_fv
                          ["FStar"; "Tactics"; "Logic"; "revert_squash"])))))
           uu___1)
let rec (l_revert_all :
  FStar_Reflection_Types.binders ->
    (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    (fun bs ->
       match bs with
       | [] ->
           Obj.magic
             (Obj.repr (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> ())))
       | uu___::tl ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Range.mk_range "FStar.Tactics.Logic.fst"
                      (Prims.of_int (42)) (Prims.of_int (21))
                      (Prims.of_int (42)) (Prims.of_int (32)))
                   (FStar_Range.mk_range "FStar.Tactics.Logic.fst"
                      (Prims.of_int (42)) (Prims.of_int (34))
                      (Prims.of_int (42)) (Prims.of_int (49)))
                   (Obj.magic (l_revert ()))
                   (fun uu___1 ->
                      (fun uu___1 -> Obj.magic (l_revert_all tl)) uu___1))))
      uu___
let (forall_intro :
  unit -> (FStar_Reflection_Types.binder, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Range.mk_range "FStar.Tactics.Logic.fst" (Prims.of_int (50))
         (Prims.of_int (4)) (Prims.of_int (50)) (Prims.of_int (31)))
      (FStar_Range.mk_range "FStar.Tactics.Logic.fst" (Prims.of_int (51))
         (Prims.of_int (4)) (Prims.of_int (51)) (Prims.of_int (12)))
      (Obj.magic
         (FStar_Tactics_Derived.apply_lemma
            (FStar_Reflection_Builtins.pack_ln
               (FStar_Reflection_Data.Tv_FVar
                  (FStar_Reflection_Builtins.pack_fv
                     ["FStar"; "Tactics"; "Logic"; "fa_intro_lem"])))))
      (fun uu___1 ->
         (fun uu___1 -> Obj.magic (FStar_Tactics_Builtins.intro ())) uu___1)
let (forall_intro_as :
  Prims.string ->
    (FStar_Reflection_Types.binder, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun s ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Range.mk_range "FStar.Tactics.Logic.fst" (Prims.of_int (55))
         (Prims.of_int (4)) (Prims.of_int (55)) (Prims.of_int (31)))
      (FStar_Range.mk_range "FStar.Tactics.Logic.fst" (Prims.of_int (56))
         (Prims.of_int (4)) (Prims.of_int (56)) (Prims.of_int (14)))
      (Obj.magic
         (FStar_Tactics_Derived.apply_lemma
            (FStar_Reflection_Builtins.pack_ln
               (FStar_Reflection_Data.Tv_FVar
                  (FStar_Reflection_Builtins.pack_fv
                     ["FStar"; "Tactics"; "Logic"; "fa_intro_lem"])))))
      (fun uu___ ->
         (fun uu___ -> Obj.magic (FStar_Tactics_Derived.intro_as s)) uu___)
let (forall_intros :
  unit ->
    (FStar_Reflection_Types.binders, unit) FStar_Tactics_Effect.tac_repr)
  = fun uu___ -> FStar_Tactics_Derived.repeat1 forall_intro
let (split : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_Derived.try_with
      (fun uu___1 ->
         match () with
         | () ->
             FStar_Tactics_Derived.apply_lemma
               (FStar_Reflection_Builtins.pack_ln
                  (FStar_Reflection_Data.Tv_FVar
                     (FStar_Reflection_Builtins.pack_fv
                        ["FStar"; "Tactics"; "Logic"; "split_lem"]))))
      (fun uu___1 ->
         (fun uu___1 ->
            Obj.magic (FStar_Tactics_Derived.fail "Could not split goal"))
           uu___1)
let (implies_intro :
  unit -> (FStar_Reflection_Types.binder, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Range.mk_range "FStar.Tactics.Logic.fst" (Prims.of_int (78))
         (Prims.of_int (4)) (Prims.of_int (78)) (Prims.of_int (32)))
      (FStar_Range.mk_range "FStar.Tactics.Logic.fst" (Prims.of_int (79))
         (Prims.of_int (4)) (Prims.of_int (79)) (Prims.of_int (12)))
      (Obj.magic
         (FStar_Tactics_Derived.apply_lemma
            (FStar_Reflection_Builtins.pack_ln
               (FStar_Reflection_Data.Tv_FVar
                  (FStar_Reflection_Builtins.pack_fv
                     ["FStar"; "Tactics"; "Logic"; "imp_intro_lem"])))))
      (fun uu___1 ->
         (fun uu___1 -> Obj.magic (FStar_Tactics_Builtins.intro ())) uu___1)
let (implies_intro_as :
  Prims.string ->
    (FStar_Reflection_Types.binder, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun s ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Range.mk_range "FStar.Tactics.Logic.fst" (Prims.of_int (82))
         (Prims.of_int (4)) (Prims.of_int (82)) (Prims.of_int (32)))
      (FStar_Range.mk_range "FStar.Tactics.Logic.fst" (Prims.of_int (83))
         (Prims.of_int (4)) (Prims.of_int (83)) (Prims.of_int (14)))
      (Obj.magic
         (FStar_Tactics_Derived.apply_lemma
            (FStar_Reflection_Builtins.pack_ln
               (FStar_Reflection_Data.Tv_FVar
                  (FStar_Reflection_Builtins.pack_fv
                     ["FStar"; "Tactics"; "Logic"; "imp_intro_lem"])))))
      (fun uu___ ->
         (fun uu___ -> Obj.magic (FStar_Tactics_Derived.intro_as s)) uu___)
let (implies_intros :
  unit ->
    (FStar_Reflection_Types.binders, unit) FStar_Tactics_Effect.tac_repr)
  = fun uu___ -> FStar_Tactics_Derived.repeat1 implies_intro
let (l_intro :
  unit -> (FStar_Reflection_Types.binder, unit) FStar_Tactics_Effect.tac_repr)
  = fun uu___ -> FStar_Tactics_Derived.or_else forall_intro implies_intro
let (l_intros :
  unit ->
    (FStar_Reflection_Types.binder Prims.list, unit)
      FStar_Tactics_Effect.tac_repr)
  = fun uu___ -> FStar_Tactics_Derived.repeat l_intro
let (squash_intro : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_Derived.apply
      (FStar_Reflection_Builtins.pack_ln
         (FStar_Reflection_Data.Tv_FVar
            (FStar_Reflection_Builtins.pack_fv
               ["FStar"; "Squash"; "return_squash"])))
let (l_exact :
  FStar_Reflection_Types.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    FStar_Tactics_Derived.try_with
      (fun uu___ -> match () with | () -> FStar_Tactics_Derived.exact t)
      (fun uu___ ->
         FStar_Tactics_Effect.tac_bind
           (FStar_Range.mk_range "FStar.Tactics.Logic.fst" (Prims.of_int (99))
              (Prims.of_int (12)) (Prims.of_int (99)) (Prims.of_int (27)))
           (FStar_Range.mk_range "FStar.Tactics.Logic.fst" (Prims.of_int (99))
              (Prims.of_int (29)) (Prims.of_int (99)) (Prims.of_int (36)))
           (Obj.magic (squash_intro ()))
           (fun uu___1 ->
              (fun uu___1 -> Obj.magic (FStar_Tactics_Derived.exact t))
                uu___1))
let (hyp :
  FStar_Reflection_Types.binder -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun b ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Range.mk_range "FStar.Tactics.Logic.fst" (Prims.of_int (101))
         (Prims.of_int (40)) (Prims.of_int (101)) (Prims.of_int (58)))
      (FStar_Range.mk_range "FStar.Tactics.Logic.fst" (Prims.of_int (101))
         (Prims.of_int (32)) (Prims.of_int (101)) (Prims.of_int (58)))
      (Obj.magic (FStar_Tactics_Derived.binder_to_term b))
      (fun uu___ -> (fun uu___ -> Obj.magic (l_exact uu___)) uu___)
let (pose_lemma :
  FStar_Reflection_Types.term ->
    (FStar_Reflection_Types.binder, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Range.mk_range "FStar.Tactics.Logic.fst" (Prims.of_int (108))
         (Prims.of_int (10)) (Prims.of_int (108)) (Prims.of_int (28)))
      (FStar_Range.mk_range "FStar.Tactics.Logic.fst" (Prims.of_int (109))
         (Prims.of_int (2)) (Prims.of_int (126)) (Prims.of_int (5)))
      (Obj.magic
         (FStar_Tactics_Effect.tac_bind
            (FStar_Range.mk_range "FStar.Tactics.Logic.fst" (Prims.of_int (108))
               (Prims.of_int (14)) (Prims.of_int (108)) (Prims.of_int (26)))
            (FStar_Range.mk_range "FStar.Tactics.Logic.fst" (Prims.of_int (108))
               (Prims.of_int (10)) (Prims.of_int (108)) (Prims.of_int (28)))
            (Obj.magic (FStar_Tactics_Derived.cur_env ()))
            (fun uu___ ->
               (fun uu___ -> Obj.magic (FStar_Tactics_Builtins.tcc uu___ t))
                 uu___)))
      (fun uu___ ->
         (fun c ->
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Range.mk_range "FStar.Tactics.Logic.fst"
                    (Prims.of_int (110)) (Prims.of_int (4))
                    (Prims.of_int (112)) (Prims.of_int (18)))
                 (FStar_Range.mk_range "FStar.Tactics.Logic.fst"
                    (Prims.of_int (109)) (Prims.of_int (2))
                    (Prims.of_int (126)) (Prims.of_int (5)))
                 (match FStar_Reflection_Builtins.inspect_comp c with
                  | FStar_Reflection_Data.C_Lemma (pre, post, uu___) ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___1 -> (pre, post))
                  | uu___ -> FStar_Tactics_Derived.fail "")
                 (fun uu___ ->
                    (fun uu___ ->
                       match uu___ with
                       | (pre, post) ->
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Range.mk_range "FStar.Tactics.Logic.fst"
                                   (Prims.of_int (114)) (Prims.of_int (13))
                                   (Prims.of_int (114)) (Prims.of_int (27)))
                                (FStar_Range.mk_range "FStar.Tactics.Logic.fst"
                                   (Prims.of_int (115)) (Prims.of_int (2))
                                   (Prims.of_int (126)) (Prims.of_int (5)))
                                (FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___1 ->
                                      FStar_Reflection_Builtins.pack_ln
                                        (FStar_Reflection_Data.Tv_App
                                           (post,
                                             ((FStar_Reflection_Builtins.pack_ln
                                                 (FStar_Reflection_Data.Tv_Const
                                                    FStar_Reflection_Data.C_Unit)),
                                               FStar_Reflection_Data.Q_Explicit)))))
                                (fun uu___1 ->
                                   (fun post1 ->
                                      Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Range.mk_range
                                              "FStar.Tactics.Logic.fst"
                                              (Prims.of_int (115))
                                              (Prims.of_int (13))
                                              (Prims.of_int (115))
                                              (Prims.of_int (30)))
                                           (FStar_Range.mk_range
                                              "FStar.Tactics.Logic.fst"
                                              (Prims.of_int (117))
                                              (Prims.of_int (2))
                                              (Prims.of_int (126))
                                              (Prims.of_int (5)))
                                           (Obj.magic
                                              (FStar_Tactics_Derived.norm_term
                                                 [] post1))
                                           (fun uu___1 ->
                                              (fun post2 ->
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Range.mk_range
                                                         "FStar.Tactics.Logic.fst"
                                                         (Prims.of_int (117))
                                                         (Prims.of_int (8))
                                                         (Prims.of_int (117))
                                                         (Prims.of_int (28)))
                                                      (FStar_Range.mk_range
                                                         "FStar.Tactics.Logic.fst"
                                                         (Prims.of_int (117))
                                                         (Prims.of_int (2))
                                                         (Prims.of_int (126))
                                                         (Prims.of_int (5)))
                                                      (Obj.magic
                                                         (FStar_Reflection_Formula.term_as_formula'
                                                            pre))
                                                      (fun uu___1 ->
                                                         (fun uu___1 ->
                                                            match uu___1 with
                                                            | FStar_Reflection_Formula.True_
                                                                ->
                                                                Obj.magic
                                                                  (FStar_Tactics_Derived.pose
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_App
                                                                    ((FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_App
                                                                    ((FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_App
                                                                    ((FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_App
                                                                    ((FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Logic";
                                                                    "__lemma_to_squash"]))),
                                                                    (pre,
                                                                    FStar_Reflection_Data.Q_Implicit)))),
                                                                    (post2,
                                                                    FStar_Reflection_Data.Q_Implicit)))),
                                                                    ((FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_Const
                                                                    FStar_Reflection_Data.C_Unit)),
                                                                    FStar_Reflection_Data.Q_Explicit)))),
                                                                    ((FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_Abs
                                                                    ((FStar_Reflection_Builtins.pack_binder
                                                                    {
                                                                    FStar_Reflection_Data.binder_bv
                                                                    =
                                                                    (FStar_Reflection_Builtins.pack_bv
                                                                    {
                                                                    FStar_Reflection_Data.bv_ppname
                                                                    =
                                                                    (FStar_Sealed.seal
                                                                    "uu___");
                                                                    FStar_Reflection_Data.bv_index
                                                                    =
                                                                    (Prims.of_int (100));
                                                                    FStar_Reflection_Data.bv_sort
                                                                    =
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["Prims";
                                                                    "unit"])))
                                                                    });
                                                                    FStar_Reflection_Data.binder_qual
                                                                    =
                                                                    FStar_Reflection_Data.Q_Explicit;
                                                                    FStar_Reflection_Data.binder_attrs
                                                                    = []
                                                                    }), t))),
                                                                    FStar_Reflection_Data.Q_Explicit)))))
                                                            | uu___2 ->
                                                                Obj.magic
                                                                  (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (37)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (126))
                                                                    (Prims.of_int (5)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Derived.tcut
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_App
                                                                    ((FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["Prims";
                                                                    "squash"]))),
                                                                    (pre,
                                                                    FStar_Reflection_Data.Q_Explicit))))))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun reqb
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (102)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (126))
                                                                    (Prims.of_int (5)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (102)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (102)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (98)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (102)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    t))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (60))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (81)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (102)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Derived.binder_to_term
                                                                    reqb))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_App
                                                                    ((FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_App
                                                                    ((FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_App
                                                                    ((FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_App
                                                                    ((FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Logic";
                                                                    "__lemma_to_squash"]))),
                                                                    (pre,
                                                                    FStar_Reflection_Data.Q_Implicit)))),
                                                                    (post2,
                                                                    FStar_Reflection_Data.Q_Implicit)))),
                                                                    (uu___4,
                                                                    FStar_Reflection_Data.Q_Explicit)))),
                                                                    ((FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_Abs
                                                                    ((FStar_Reflection_Builtins.pack_binder
                                                                    {
                                                                    FStar_Reflection_Data.binder_bv
                                                                    =
                                                                    (FStar_Reflection_Builtins.pack_bv
                                                                    {
                                                                    FStar_Reflection_Data.bv_ppname
                                                                    =
                                                                    (FStar_Sealed.seal
                                                                    "uu___");
                                                                    FStar_Reflection_Data.bv_index
                                                                    =
                                                                    (Prims.of_int (107));
                                                                    FStar_Reflection_Data.bv_sort
                                                                    =
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["Prims";
                                                                    "unit"])))
                                                                    });
                                                                    FStar_Reflection_Data.binder_qual
                                                                    =
                                                                    FStar_Reflection_Data.Q_Explicit;
                                                                    FStar_Reflection_Data.binder_attrs
                                                                    = []
                                                                    }),
                                                                    uu___3))),
                                                                    FStar_Reflection_Data.Q_Explicit)))))))
                                                                    uu___3)))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Derived.pose
                                                                    uu___3))
                                                                    uu___3)))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun b ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (11)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (126))
                                                                    (Prims.of_int (5)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Derived.flip
                                                                    ()))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (27)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (9)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (27)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (27)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Derived.trytac
                                                                    FStar_Tactics_Derived.trivial))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    ()))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    b))))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                           uu___1))) uu___1)))
                                     uu___1))) uu___))) uu___)
let (explode : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Range.mk_range "FStar.Tactics.Logic.fst" (Prims.of_int (129))
         (Prims.of_int (11)) (Prims.of_int (131)) (Prims.of_int (64)))
      (FStar_Range.mk_range "FStar.Tactics.Logic.fst" (Prims.of_int (129))
         (Prims.of_int (4)) (Prims.of_int (131)) (Prims.of_int (64)))
      (Obj.magic
         (FStar_Tactics_Derived.repeatseq
            (fun uu___1 ->
               FStar_Tactics_Derived.first
                 [(fun uu___2 ->
                     FStar_Tactics_Effect.tac_bind
                       (FStar_Range.mk_range "FStar.Tactics.Logic.fst"
                          (Prims.of_int (130)) (Prims.of_int (50))
                          (Prims.of_int (130)) (Prims.of_int (62)))
                       (FStar_Range.mk_range "FStar.Tactics.Logic.fst"
                          (Prims.of_int (130)) (Prims.of_int (43))
                          (Prims.of_int (130)) (Prims.of_int (62)))
                       (Obj.magic (l_intro ()))
                       (fun uu___3 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___4 -> ())));
                 (fun uu___2 ->
                    FStar_Tactics_Effect.tac_bind
                      (FStar_Range.mk_range "FStar.Tactics.Logic.fst"
                         (Prims.of_int (131)) (Prims.of_int (50))
                         (Prims.of_int (131)) (Prims.of_int (60)))
                      (FStar_Range.mk_range "FStar.Tactics.Logic.fst"
                         (Prims.of_int (131)) (Prims.of_int (43))
                         (Prims.of_int (131)) (Prims.of_int (60)))
                      (Obj.magic (split ()))
                      (fun uu___3 ->
                         FStar_Tactics_Effect.lift_div_tac (fun uu___4 -> ())))])))
      (fun uu___1 -> FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> ()))
let rec (visit :
  (unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) ->
    (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun callback ->
    FStar_Tactics_Derived.focus
      (fun uu___ ->
         FStar_Tactics_Derived.or_else callback
           (fun uu___1 ->
              FStar_Tactics_Effect.tac_bind
                (FStar_Range.mk_range "FStar.Tactics.Logic.fst"
                   (Prims.of_int (137)) (Prims.of_int (28))
                   (Prims.of_int (137)) (Prims.of_int (39)))
                (FStar_Range.mk_range "FStar.Tactics.Logic.fst"
                   (Prims.of_int (138)) (Prims.of_int (20))
                   (Prims.of_int (148)) (Prims.of_int (26)))
                (Obj.magic (FStar_Tactics_Derived.cur_goal ()))
                (fun uu___2 ->
                   (fun g ->
                      Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Range.mk_range "FStar.Tactics.Logic.fst"
                              (Prims.of_int (138)) (Prims.of_int (26))
                              (Prims.of_int (138)) (Prims.of_int (43)))
                           (FStar_Range.mk_range "FStar.Tactics.Logic.fst"
                              (Prims.of_int (138)) (Prims.of_int (20))
                              (Prims.of_int (148)) (Prims.of_int (26)))
                           (Obj.magic
                              (FStar_Reflection_Formula.term_as_formula g))
                           (fun uu___2 ->
                              (fun uu___2 ->
                                 match uu___2 with
                                 | FStar_Reflection_Formula.Forall (b, phi)
                                     ->
                                     Obj.magic
                                       (Obj.repr
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.Logic.fst"
                                                (Prims.of_int (140))
                                                (Prims.of_int (38))
                                                (Prims.of_int (140))
                                                (Prims.of_int (54)))
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.Logic.fst"
                                                (Prims.of_int (141))
                                                (Prims.of_int (24))
                                                (Prims.of_int (141))
                                                (Prims.of_int (87)))
                                             (Obj.magic (forall_intros ()))
                                             (fun uu___3 ->
                                                (fun binders ->
                                                   Obj.magic
                                                     (FStar_Tactics_Derived.seq
                                                        (fun uu___3 ->
                                                           visit callback)
                                                        (fun uu___3 ->
                                                           l_revert_all
                                                             binders)))
                                                  uu___3)))
                                 | FStar_Reflection_Formula.And (p, q) ->
                                     Obj.magic
                                       (Obj.repr
                                          (FStar_Tactics_Derived.seq split
                                             (fun uu___3 -> visit callback)))
                                 | FStar_Reflection_Formula.Implies (p, q) ->
                                     Obj.magic
                                       (Obj.repr
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.Logic.fst"
                                                (Prims.of_int (145))
                                                (Prims.of_int (32))
                                                (Prims.of_int (145))
                                                (Prims.of_int (48)))
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.Logic.fst"
                                                (Prims.of_int (146))
                                                (Prims.of_int (24))
                                                (Prims.of_int (146))
                                                (Prims.of_int (63)))
                                             (Obj.magic (implies_intro ()))
                                             (fun uu___3 ->
                                                (fun uu___3 ->
                                                   Obj.magic
                                                     (FStar_Tactics_Derived.seq
                                                        (fun uu___4 ->
                                                           visit callback)
                                                        l_revert)) uu___3)))
                                 | uu___3 ->
                                     Obj.magic
                                       (Obj.repr
                                          (FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___4 -> ())))) uu___2)))
                     uu___2)))
let rec (simplify_eq_implication :
  unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Range.mk_range "FStar.Tactics.Logic.fst" (Prims.of_int (153))
         (Prims.of_int (12)) (Prims.of_int (153)) (Prims.of_int (22)))
      (FStar_Range.mk_range "FStar.Tactics.Logic.fst" (Prims.of_int (154))
         (Prims.of_int (4)) (Prims.of_int (163)) (Prims.of_int (37)))
      (Obj.magic (FStar_Tactics_Derived.cur_env ()))
      (fun uu___1 ->
         (fun e ->
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Range.mk_range "FStar.Tactics.Logic.fst"
                    (Prims.of_int (154)) (Prims.of_int (12))
                    (Prims.of_int (154)) (Prims.of_int (23)))
                 (FStar_Range.mk_range "FStar.Tactics.Logic.fst"
                    (Prims.of_int (155)) (Prims.of_int (4))
                    (Prims.of_int (163)) (Prims.of_int (37)))
                 (Obj.magic (FStar_Tactics_Derived.cur_goal ()))
                 (fun uu___1 ->
                    (fun g ->
                       Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Range.mk_range "FStar.Tactics.Logic.fst"
                               (Prims.of_int (155)) (Prims.of_int (12))
                               (Prims.of_int (155)) (Prims.of_int (43)))
                            (FStar_Range.mk_range "FStar.Tactics.Logic.fst"
                               (Prims.of_int (156)) (Prims.of_int (4))
                               (Prims.of_int (163)) (Prims.of_int (37)))
                            (Obj.magic
                               (FStar_Tactics_Derived.destruct_equality_implication
                                  g))
                            (fun uu___1 ->
                               (fun r ->
                                  match r with
                                  | FStar_Pervasives_Native.None ->
                                      Obj.magic
                                        (Obj.repr
                                           (FStar_Tactics_Derived.fail
                                              "Not an equality implication"))
                                  | FStar_Pervasives_Native.Some
                                      (uu___1, rhs) ->
                                      Obj.magic
                                        (Obj.repr
                                           (FStar_Tactics_Effect.tac_bind
                                              (FStar_Range.mk_range
                                                 "FStar.Tactics.Logic.fst"
                                                 (Prims.of_int (160))
                                                 (Prims.of_int (19))
                                                 (Prims.of_int (160))
                                                 (Prims.of_int (35)))
                                              (FStar_Range.mk_range
                                                 "FStar.Tactics.Logic.fst"
                                                 (Prims.of_int (161))
                                                 (Prims.of_int (8))
                                                 (Prims.of_int (163))
                                                 (Prims.of_int (37)))
                                              (Obj.magic (implies_intro ()))
                                              (fun uu___2 ->
                                                 (fun eq_h ->
                                                    Obj.magic
                                                      (FStar_Tactics_Effect.tac_bind
                                                         (FStar_Range.mk_range
                                                            "FStar.Tactics.Logic.fst"
                                                            (Prims.of_int (161))
                                                            (Prims.of_int (8))
                                                            (Prims.of_int (161))
                                                            (Prims.of_int (20)))
                                                         (FStar_Range.mk_range
                                                            "FStar.Tactics.Logic.fst"
                                                            (Prims.of_int (162))
                                                            (Prims.of_int (8))
                                                            (Prims.of_int (163))
                                                            (Prims.of_int (37)))
                                                         (Obj.magic
                                                            (FStar_Tactics_Builtins.rewrite
                                                               eq_h))
                                                         (fun uu___2 ->
                                                            (fun uu___2 ->
                                                               Obj.magic
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (162))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (162))
                                                                    (Prims.of_int (20)))
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (163))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (163))
                                                                    (Prims.of_int (37)))
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Tactics_Builtins.clear_top
                                                                    ()))
                                                                    (
                                                                    fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (visit
                                                                    simplify_eq_implication))
                                                                    uu___3)))
                                                              uu___2)))
                                                   uu___2)))) uu___1)))
                      uu___1))) uu___1)
let (rewrite_all_equalities :
  unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ -> visit simplify_eq_implication
let rec (unfold_definition_and_simplify_eq :
  FStar_Reflection_Types.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun tm ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Range.mk_range "FStar.Tactics.Logic.fst" (Prims.of_int (169))
         (Prims.of_int (12)) (Prims.of_int (169)) (Prims.of_int (23)))
      (FStar_Range.mk_range "FStar.Tactics.Logic.fst" (Prims.of_int (170))
         (Prims.of_int (4)) (Prims.of_int (184)) (Prims.of_int (11)))
      (Obj.magic (FStar_Tactics_Derived.cur_goal ()))
      (fun uu___ ->
         (fun g ->
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Range.mk_range "FStar.Tactics.Logic.fst"
                    (Prims.of_int (170)) (Prims.of_int (10))
                    (Prims.of_int (170)) (Prims.of_int (27)))
                 (FStar_Range.mk_range "FStar.Tactics.Logic.fst"
                    (Prims.of_int (170)) (Prims.of_int (4))
                    (Prims.of_int (184)) (Prims.of_int (11)))
                 (Obj.magic (FStar_Reflection_Formula.term_as_formula g))
                 (fun uu___ ->
                    (fun uu___ ->
                       match uu___ with
                       | FStar_Reflection_Formula.App (hd, arg) ->
                           Obj.magic
                             (Obj.repr
                                (if FStar_Reflection_Builtins.term_eq hd tm
                                 then
                                   Obj.repr
                                     (FStar_Tactics_Derived.trivial ())
                                 else
                                   Obj.repr
                                     (FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___2 -> ()))))
                       | uu___1 ->
                           Obj.magic
                             (Obj.repr
                                (FStar_Tactics_Effect.tac_bind
                                   (FStar_Range.mk_range "FStar.Tactics.Logic.fst"
                                      (Prims.of_int (176))
                                      (Prims.of_int (16))
                                      (Prims.of_int (176))
                                      (Prims.of_int (47)))
                                   (FStar_Range.mk_range "FStar.Tactics.Logic.fst"
                                      (Prims.of_int (177)) (Prims.of_int (8))
                                      (Prims.of_int (183))
                                      (Prims.of_int (66)))
                                   (Obj.magic
                                      (FStar_Tactics_Derived.destruct_equality_implication
                                         g))
                                   (fun uu___2 ->
                                      (fun r ->
                                         match r with
                                         | FStar_Pervasives_Native.None ->
                                             Obj.magic
                                               (Obj.repr
                                                  (FStar_Tactics_Derived.fail
                                                     "Not an equality implication"))
                                         | FStar_Pervasives_Native.Some
                                             (uu___2, rhs) ->
                                             Obj.magic
                                               (Obj.repr
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Range.mk_range
                                                        "FStar.Tactics.Logic.fst"
                                                        (Prims.of_int (180))
                                                        (Prims.of_int (23))
                                                        (Prims.of_int (180))
                                                        (Prims.of_int (39)))
                                                     (FStar_Range.mk_range
                                                        "FStar.Tactics.Logic.fst"
                                                        (Prims.of_int (181))
                                                        (Prims.of_int (12))
                                                        (Prims.of_int (183))
                                                        (Prims.of_int (66)))
                                                     (Obj.magic
                                                        (implies_intro ()))
                                                     (fun uu___3 ->
                                                        (fun eq_h ->
                                                           Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Range.mk_range
                                                                   "FStar.Tactics.Logic.fst"
                                                                   (Prims.of_int (181))
                                                                   (Prims.of_int (12))
                                                                   (Prims.of_int (181))
                                                                   (Prims.of_int (24)))
                                                                (FStar_Range.mk_range
                                                                   "FStar.Tactics.Logic.fst"
                                                                   (Prims.of_int (182))
                                                                   (Prims.of_int (12))
                                                                   (Prims.of_int (183))
                                                                   (Prims.of_int (66)))
                                                                (Obj.magic
                                                                   (FStar_Tactics_Builtins.rewrite
                                                                    eq_h))
                                                                (fun uu___3
                                                                   ->
                                                                   (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (182))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (182))
                                                                    (Prims.of_int (24)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (183))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (183))
                                                                    (Prims.of_int (66)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Builtins.clear_top
                                                                    ()))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (visit
                                                                    (fun
                                                                    uu___5 ->
                                                                    unfold_definition_and_simplify_eq
                                                                    tm)))
                                                                    uu___4)))
                                                                    uu___3)))
                                                          uu___3)))) uu___2))))
                      uu___))) uu___)
let (unsquash :
  FStar_Reflection_Types.term ->
    (FStar_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Range.mk_range "FStar.Tactics.Logic.fst" (Prims.of_int (192))
         (Prims.of_int (12)) (Prims.of_int (192)) (Prims.of_int (18)))
      (FStar_Range.mk_range "FStar.Tactics.Logic.fst" (Prims.of_int (193))
         (Prims.of_int (4)) (Prims.of_int (195)) (Prims.of_int (37)))
      (FStar_Tactics_Effect.lift_div_tac
         (fun uu___ ->
            FStar_Reflection_Builtins.pack_ln
              (FStar_Reflection_Data.Tv_FVar
                 (FStar_Reflection_Builtins.pack_fv
                    ["FStar"; "Tactics"; "Logic"; "vbind"]))))
      (fun uu___ ->
         (fun v ->
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Range.mk_range "FStar.Tactics.Logic.fst"
                    (Prims.of_int (193)) (Prims.of_int (4))
                    (Prims.of_int (193)) (Prims.of_int (32)))
                 (FStar_Range.mk_range "FStar.Tactics.Logic.fst"
                    (Prims.of_int (194)) (Prims.of_int (4))
                    (Prims.of_int (195)) (Prims.of_int (37)))
                 (Obj.magic
                    (FStar_Tactics_Derived.apply_lemma
                       (FStar_Reflection_Derived.mk_e_app v [t])))
                 (fun uu___ ->
                    (fun uu___ ->
                       Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Range.mk_range "FStar.Tactics.Logic.fst"
                               (Prims.of_int (194)) (Prims.of_int (12))
                               (Prims.of_int (194)) (Prims.of_int (20)))
                            (FStar_Range.mk_range "FStar.Tactics.Logic.fst"
                               (Prims.of_int (195)) (Prims.of_int (4))
                               (Prims.of_int (195)) (Prims.of_int (37)))
                            (Obj.magic (FStar_Tactics_Builtins.intro ()))
                            (fun b ->
                               FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___1 ->
                                    FStar_Reflection_Builtins.pack_ln
                                      (FStar_Reflection_Data.Tv_Var
                                         (FStar_Reflection_Derived.bv_of_binder
                                            b)))))) uu___))) uu___)
let (cases_or :
  FStar_Reflection_Types.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun o ->
    FStar_Tactics_Derived.apply_lemma
      (FStar_Reflection_Derived.mk_e_app
         (FStar_Reflection_Builtins.pack_ln
            (FStar_Reflection_Data.Tv_FVar
               (FStar_Reflection_Builtins.pack_fv
                  ["FStar"; "Tactics"; "Logic"; "or_ind"]))) [o])
let (cases_bool :
  FStar_Reflection_Types.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun b ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Range.mk_range "FStar.Tactics.Logic.fst" (Prims.of_int (213))
         (Prims.of_int (13)) (Prims.of_int (213)) (Prims.of_int (22)))
      (FStar_Range.mk_range "FStar.Tactics.Logic.fst" (Prims.of_int (214))
         (Prims.of_int (4)) (Prims.of_int (215)) (Prims.of_int (104)))
      (FStar_Tactics_Effect.lift_div_tac
         (fun uu___ ->
            FStar_Reflection_Builtins.pack_ln
              (FStar_Reflection_Data.Tv_FVar
                 (FStar_Reflection_Builtins.pack_fv
                    ["FStar"; "Tactics"; "Logic"; "bool_ind"]))))
      (fun uu___ ->
         (fun bi ->
            Obj.magic
              (FStar_Tactics_Derived.seq
                 (fun uu___ ->
                    FStar_Tactics_Derived.apply_lemma
                      (FStar_Reflection_Derived.mk_e_app bi [b]))
                 (fun uu___ ->
                    FStar_Tactics_Effect.tac_bind
                      (FStar_Range.mk_range "FStar.Tactics.Logic.fst"
                         (Prims.of_int (215)) (Prims.of_int (27))
                         (Prims.of_int (215)) (Prims.of_int (97)))
                      (FStar_Range.mk_range "FStar.Tactics.Logic.fst"
                         (Prims.of_int (215)) (Prims.of_int (101))
                         (Prims.of_int (215)) (Prims.of_int (103)))
                      (Obj.magic
                         (FStar_Tactics_Derived.trytac
                            (fun uu___1 ->
                               FStar_Tactics_Effect.tac_bind
                                 (FStar_Range.mk_range "FStar.Tactics.Logic.fst"
                                    (Prims.of_int (215)) (Prims.of_int (53))
                                    (Prims.of_int (215)) (Prims.of_int (69)))
                                 (FStar_Range.mk_range "FStar.Tactics.Logic.fst"
                                    (Prims.of_int (215)) (Prims.of_int (73))
                                    (Prims.of_int (215)) (Prims.of_int (96)))
                                 (Obj.magic (implies_intro ()))
                                 (fun uu___2 ->
                                    (fun b1 ->
                                       Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Range.mk_range
                                               "FStar.Tactics.Logic.fst"
                                               (Prims.of_int (215))
                                               (Prims.of_int (73))
                                               (Prims.of_int (215))
                                               (Prims.of_int (82)))
                                            (FStar_Range.mk_range
                                               "FStar.Tactics.Logic.fst"
                                               (Prims.of_int (215))
                                               (Prims.of_int (84))
                                               (Prims.of_int (215))
                                               (Prims.of_int (96)))
                                            (Obj.magic
                                               (FStar_Tactics_Builtins.rewrite
                                                  b1))
                                            (fun uu___2 ->
                                               (fun uu___2 ->
                                                  Obj.magic
                                                    (FStar_Tactics_Builtins.clear_top
                                                       ())) uu___2))) uu___2))))
                      (fun uu___1 ->
                         FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> ())))))
           uu___)
let (left : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_Derived.apply_lemma
      (FStar_Reflection_Builtins.pack_ln
         (FStar_Reflection_Data.Tv_FVar
            (FStar_Reflection_Builtins.pack_fv
               ["FStar"; "Tactics"; "Logic"; "or_intro_1"])))
let (right : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_Derived.apply_lemma
      (FStar_Reflection_Builtins.pack_ln
         (FStar_Reflection_Data.Tv_FVar
            (FStar_Reflection_Builtins.pack_fv
               ["FStar"; "Tactics"; "Logic"; "or_intro_2"])))
let (and_elim :
  FStar_Reflection_Types.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    FStar_Tactics_Derived.try_with
      (fun uu___ ->
         match () with
         | () ->
             FStar_Tactics_Derived.apply_lemma
               (FStar_Reflection_Builtins.pack_ln
                  (FStar_Reflection_Data.Tv_App
                     ((FStar_Reflection_Builtins.pack_ln
                         (FStar_Reflection_Data.Tv_FVar
                            (FStar_Reflection_Builtins.pack_fv
                               ["FStar"; "Tactics"; "Logic"; "__and_elim"]))),
                       (t, FStar_Reflection_Data.Q_Explicit)))))
      (fun uu___ ->
         FStar_Tactics_Derived.apply_lemma
           (FStar_Reflection_Builtins.pack_ln
              (FStar_Reflection_Data.Tv_App
                 ((FStar_Reflection_Builtins.pack_ln
                     (FStar_Reflection_Data.Tv_FVar
                        (FStar_Reflection_Builtins.pack_fv
                           ["FStar"; "Tactics"; "Logic"; "__and_elim'"]))),
                   (t, FStar_Reflection_Data.Q_Explicit)))))
let (destruct_and :
  FStar_Reflection_Types.term ->
    ((FStar_Reflection_Types.binder * FStar_Reflection_Types.binder), 
      unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Range.mk_range "FStar.Tactics.Logic.fst" (Prims.of_int (248))
         (Prims.of_int (4)) (Prims.of_int (248)) (Prims.of_int (14)))
      (FStar_Range.mk_range "FStar.Tactics.Logic.fst" (Prims.of_int (249))
         (Prims.of_int (4)) (Prims.of_int (249)) (Prims.of_int (40)))
      (Obj.magic (and_elim t))
      (fun uu___ ->
         (fun uu___ ->
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Range.mk_range "FStar.Tactics.Logic.fst"
                    (Prims.of_int (249)) (Prims.of_int (5))
                    (Prims.of_int (249)) (Prims.of_int (21)))
                 (FStar_Range.mk_range "FStar.Tactics.Logic.fst"
                    (Prims.of_int (249)) (Prims.of_int (4))
                    (Prims.of_int (249)) (Prims.of_int (40)))
                 (Obj.magic (implies_intro ()))
                 (fun uu___1 ->
                    (fun uu___1 ->
                       Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Range.mk_range "FStar.Tactics.Logic.fst"
                               (Prims.of_int (249)) (Prims.of_int (23))
                               (Prims.of_int (249)) (Prims.of_int (39)))
                            (FStar_Range.mk_range "FStar.Tactics.Logic.fst"
                               (Prims.of_int (249)) (Prims.of_int (4))
                               (Prims.of_int (249)) (Prims.of_int (40)))
                            (Obj.magic (implies_intro ()))
                            (fun uu___2 ->
                               FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___3 -> (uu___1, uu___2))))) uu___1)))
           uu___)
let (witness :
  FStar_Reflection_Types.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Range.mk_range "FStar.Tactics.Logic.fst" (Prims.of_int (255))
         (Prims.of_int (4)) (Prims.of_int (255)) (Prims.of_int (26)))
      (FStar_Range.mk_range "FStar.Tactics.Logic.fst" (Prims.of_int (256))
         (Prims.of_int (4)) (Prims.of_int (256)) (Prims.of_int (11)))
      (Obj.magic
         (FStar_Tactics_Derived.apply_raw
            (FStar_Reflection_Builtins.pack_ln
               (FStar_Reflection_Data.Tv_FVar
                  (FStar_Reflection_Builtins.pack_fv
                     ["FStar"; "Tactics"; "Logic"; "__witness"])))))
      (fun uu___ ->
         (fun uu___ -> Obj.magic (FStar_Tactics_Derived.exact t)) uu___)
let (elim_exists :
  FStar_Reflection_Types.term ->
    ((FStar_Reflection_Types.binder * FStar_Reflection_Types.binder), 
      unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Range.mk_range "FStar.Tactics.Logic.fst" (Prims.of_int (265))
         (Prims.of_int (2)) (Prims.of_int (265)) (Prims.of_int (41)))
      (FStar_Range.mk_range "FStar.Tactics.Logic.fst" (Prims.of_int (266))
         (Prims.of_int (2)) (Prims.of_int (268)) (Prims.of_int (9)))
      (Obj.magic
         (FStar_Tactics_Derived.apply_lemma
            (FStar_Reflection_Builtins.pack_ln
               (FStar_Reflection_Data.Tv_App
                  ((FStar_Reflection_Builtins.pack_ln
                      (FStar_Reflection_Data.Tv_FVar
                         (FStar_Reflection_Builtins.pack_fv
                            ["FStar"; "Tactics"; "Logic"; "__elim_exists'"]))),
                    (t, FStar_Reflection_Data.Q_Explicit))))))
      (fun uu___ ->
         (fun uu___ ->
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Range.mk_range "FStar.Tactics.Logic.fst"
                    (Prims.of_int (266)) (Prims.of_int (10))
                    (Prims.of_int (266)) (Prims.of_int (18)))
                 (FStar_Range.mk_range "FStar.Tactics.Logic.fst"
                    (Prims.of_int (267)) (Prims.of_int (2))
                    (Prims.of_int (268)) (Prims.of_int (9)))
                 (Obj.magic (FStar_Tactics_Builtins.intro ()))
                 (fun uu___1 ->
                    (fun x ->
                       Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Range.mk_range "FStar.Tactics.Logic.fst"
                               (Prims.of_int (267)) (Prims.of_int (11))
                               (Prims.of_int (267)) (Prims.of_int (19)))
                            (FStar_Range.mk_range "FStar.Tactics.Logic.fst"
                               (Prims.of_int (268)) (Prims.of_int (2))
                               (Prims.of_int (268)) (Prims.of_int (9)))
                            (Obj.magic (FStar_Tactics_Builtins.intro ()))
                            (fun pf ->
                               FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___1 -> (x, pf))))) uu___1))) uu___)
let (instantiate :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term ->
      (FStar_Reflection_Types.binder, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun fa ->
    fun x ->
      FStar_Tactics_Derived.try_with
        (fun uu___ ->
           match () with
           | () ->
               FStar_Tactics_Derived.pose
                 (FStar_Reflection_Builtins.pack_ln
                    (FStar_Reflection_Data.Tv_App
                       ((FStar_Reflection_Builtins.pack_ln
                           (FStar_Reflection_Data.Tv_App
                              ((FStar_Reflection_Builtins.pack_ln
                                  (FStar_Reflection_Data.Tv_FVar
                                     (FStar_Reflection_Builtins.pack_fv
                                        ["FStar";
                                        "Tactics";
                                        "Logic";
                                        "__forall_inst_sq"]))),
                                (fa, FStar_Reflection_Data.Q_Explicit)))),
                         (x, FStar_Reflection_Data.Q_Explicit)))))
        (fun uu___ ->
           FStar_Tactics_Derived.try_with
             (fun uu___1 ->
                match () with
                | () ->
                    FStar_Tactics_Derived.pose
                      (FStar_Reflection_Builtins.pack_ln
                         (FStar_Reflection_Data.Tv_App
                            ((FStar_Reflection_Builtins.pack_ln
                                (FStar_Reflection_Data.Tv_App
                                   ((FStar_Reflection_Builtins.pack_ln
                                       (FStar_Reflection_Data.Tv_FVar
                                          (FStar_Reflection_Builtins.pack_fv
                                             ["FStar";
                                             "Tactics";
                                             "Logic";
                                             "__forall_inst"]))),
                                     (fa, FStar_Reflection_Data.Q_Explicit)))),
                              (x, FStar_Reflection_Data.Q_Explicit)))))
             (fun uu___1 ->
                (fun uu___1 ->
                   Obj.magic
                     (FStar_Tactics_Derived.fail "could not instantiate"))
                  uu___1))
let (instantiate_as :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term ->
      Prims.string ->
        (FStar_Reflection_Types.binder, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun fa ->
    fun x ->
      fun s ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Range.mk_range "FStar.Tactics.Logic.fst" (Prims.of_int (285))
             (Prims.of_int (12)) (Prims.of_int (285)) (Prims.of_int (28)))
          (FStar_Range.mk_range "FStar.Tactics.Logic.fst" (Prims.of_int (286))
             (Prims.of_int (4)) (Prims.of_int (286)) (Prims.of_int (17)))
          (Obj.magic (instantiate fa x))
          (fun uu___ ->
             (fun b -> Obj.magic (FStar_Tactics_Builtins.rename_to b s))
               uu___)
let rec (sk_binder' :
  FStar_Reflection_Types.binders ->
    FStar_Reflection_Types.binder ->
      ((FStar_Reflection_Types.binders * FStar_Reflection_Types.binder),
        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun acc ->
    fun b ->
      FStar_Tactics_Derived.focus
        (fun uu___ ->
           FStar_Tactics_Derived.try_with
             (fun uu___1 ->
                match () with
                | () ->
                    FStar_Tactics_Effect.tac_bind
                      (FStar_Range.mk_range "FStar.Tactics.Logic.fst"
                         (Prims.of_int (297)) (Prims.of_int (6))
                         (Prims.of_int (297)) (Prims.of_int (52)))
                      (FStar_Range.mk_range "FStar.Tactics.Logic.fst"
                         (Prims.of_int (298)) (Prims.of_int (6))
                         (Prims.of_int (302)) (Prims.of_int (29)))
                      (Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Range.mk_range "FStar.Tactics.Logic.fst"
                               (Prims.of_int (297)) (Prims.of_int (18))
                               (Prims.of_int (297)) (Prims.of_int (52)))
                            (FStar_Range.mk_range "FStar.Tactics.Logic.fst"
                               (Prims.of_int (297)) (Prims.of_int (6))
                               (Prims.of_int (297)) (Prims.of_int (52)))
                            (Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Range.mk_range "FStar.Tactics.Logic.fst"
                                     (Prims.of_int (297)) (Prims.of_int (31))
                                     (Prims.of_int (297)) (Prims.of_int (49)))
                                  (FStar_Range.mk_range "FStar.Tactics.Logic.fst"
                                     (Prims.of_int (297)) (Prims.of_int (18))
                                     (Prims.of_int (297)) (Prims.of_int (52)))
                                  (Obj.magic
                                     (FStar_Tactics_Derived.binder_to_term b))
                                  (fun uu___2 ->
                                     FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___3 ->
                                          FStar_Reflection_Builtins.pack_ln
                                            (FStar_Reflection_Data.Tv_App
                                               ((FStar_Reflection_Builtins.pack_ln
                                                   (FStar_Reflection_Data.Tv_FVar
                                                      (FStar_Reflection_Builtins.pack_fv
                                                         ["FStar";
                                                         "Tactics";
                                                         "Logic";
                                                         "sklem0"]))),
                                                 (uu___2,
                                                   FStar_Reflection_Data.Q_Explicit)))))))
                            (fun uu___2 ->
                               (fun uu___2 ->
                                  Obj.magic
                                    (FStar_Tactics_Derived.apply_lemma uu___2))
                                 uu___2)))
                      (fun uu___2 ->
                         (fun uu___2 ->
                            Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Range.mk_range "FStar.Tactics.Logic.fst"
                                    (Prims.of_int (298)) (Prims.of_int (6))
                                    (Prims.of_int (298)) (Prims.of_int (38)))
                                 (FStar_Range.mk_range "FStar.Tactics.Logic.fst"
                                    (Prims.of_int (299)) (Prims.of_int (6))
                                    (Prims.of_int (302)) (Prims.of_int (29)))
                                 (Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Range.mk_range
                                          "FStar.Tactics.Logic.fst"
                                          (Prims.of_int (298))
                                          (Prims.of_int (9))
                                          (Prims.of_int (298))
                                          (Prims.of_int (23)))
                                       (FStar_Range.mk_range
                                          "FStar.Tactics.Logic.fst"
                                          (Prims.of_int (298))
                                          (Prims.of_int (6))
                                          (Prims.of_int (298))
                                          (Prims.of_int (38)))
                                       (Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.Logic.fst"
                                                (Prims.of_int (298))
                                                (Prims.of_int (9))
                                                (Prims.of_int (298))
                                                (Prims.of_int (18)))
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.Logic.fst"
                                                (Prims.of_int (298))
                                                (Prims.of_int (9))
                                                (Prims.of_int (298))
                                                (Prims.of_int (23)))
                                             (Obj.magic
                                                (FStar_Tactics_Derived.ngoals
                                                   ()))
                                             (fun uu___3 ->
                                                FStar_Tactics_Effect.lift_div_tac
                                                  (fun uu___4 ->
                                                     uu___3 <> Prims.int_one))))
                                       (fun uu___3 ->
                                          if uu___3
                                          then
                                            FStar_Tactics_Derived.fail "no"
                                          else
                                            FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___5 -> ()))))
                                 (fun uu___3 ->
                                    (fun uu___3 ->
                                       Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Range.mk_range
                                               "FStar.Tactics.Logic.fst"
                                               (Prims.of_int (299))
                                               (Prims.of_int (6))
                                               (Prims.of_int (299))
                                               (Prims.of_int (13)))
                                            (FStar_Range.mk_range
                                               "FStar.Tactics.Logic.fst"
                                               (Prims.of_int (300))
                                               (Prims.of_int (6))
                                               (Prims.of_int (302))
                                               (Prims.of_int (29)))
                                            (Obj.magic
                                               (FStar_Tactics_Builtins.clear
                                                  b))
                                            (fun uu___4 ->
                                               (fun uu___4 ->
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Range.mk_range
                                                          "FStar.Tactics.Logic.fst"
                                                          (Prims.of_int (300))
                                                          (Prims.of_int (15))
                                                          (Prims.of_int (300))
                                                          (Prims.of_int (30)))
                                                       (FStar_Range.mk_range
                                                          "FStar.Tactics.Logic.fst"
                                                          (Prims.of_int (301))
                                                          (Prims.of_int (6))
                                                          (Prims.of_int (302))
                                                          (Prims.of_int (29)))
                                                       (Obj.magic
                                                          (forall_intro ()))
                                                       (fun uu___5 ->
                                                          (fun bx ->
                                                             Obj.magic
                                                               (FStar_Tactics_Effect.tac_bind
                                                                  (FStar_Range.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (301))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (301))
                                                                    (Prims.of_int (31)))
                                                                  (FStar_Range.mk_range
                                                                    "FStar.Tactics.Logic.fst"
                                                                    (Prims.of_int (302))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (302))
                                                                    (Prims.of_int (29)))
                                                                  (Obj.magic
                                                                    (implies_intro
                                                                    ()))
                                                                  (fun uu___5
                                                                    ->
                                                                    (fun b'
                                                                    ->
                                                                    Obj.magic
                                                                    (sk_binder'
                                                                    (bx ::
                                                                    acc) b'))
                                                                    uu___5)))
                                                            uu___5))) uu___4)))
                                      uu___3))) uu___2))
             (fun uu___1 ->
                (fun uu___1 ->
                   Obj.magic
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___2 -> (acc, b)))) uu___1))
let (sk_binder :
  FStar_Reflection_Types.binder ->
    ((FStar_Reflection_Types.binders * FStar_Reflection_Types.binder), 
      unit) FStar_Tactics_Effect.tac_repr)
  = fun b -> sk_binder' [] b
let (skolem :
  unit ->
    ((FStar_Reflection_Types.binders * FStar_Reflection_Types.binder)
       Prims.list,
      unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Range.mk_range "FStar.Tactics.Logic.fst" (Prims.of_int (311))
         (Prims.of_int (11)) (Prims.of_int (311)) (Prims.of_int (38)))
      (FStar_Range.mk_range "FStar.Tactics.Logic.fst" (Prims.of_int (312))
         (Prims.of_int (2)) (Prims.of_int (312)) (Prims.of_int (18)))
      (Obj.magic
         (FStar_Tactics_Effect.tac_bind
            (FStar_Range.mk_range "FStar.Tactics.Logic.fst" (Prims.of_int (311))
               (Prims.of_int (26)) (Prims.of_int (311)) (Prims.of_int (38)))
            (FStar_Range.mk_range "FStar.Tactics.Logic.fst" (Prims.of_int (311))
               (Prims.of_int (11)) (Prims.of_int (311)) (Prims.of_int (38)))
            (Obj.magic (FStar_Tactics_Derived.cur_env ()))
            (fun uu___1 ->
               FStar_Tactics_Effect.lift_div_tac
                 (fun uu___2 ->
                    FStar_Reflection_Builtins.binders_of_env uu___1))))
      (fun uu___1 ->
         (fun bs -> Obj.magic (FStar_Tactics_Util.map sk_binder bs)) uu___1)
let (easy_fill : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Range.mk_range "FStar.Tactics.Logic.fst" (Prims.of_int (321))
         (Prims.of_int (12)) (Prims.of_int (321)) (Prims.of_int (24)))
      (FStar_Range.mk_range "FStar.Tactics.Logic.fst" (Prims.of_int (323))
         (Prims.of_int (4)) (Prims.of_int (324)) (Prims.of_int (10)))
      (Obj.magic (FStar_Tactics_Derived.repeat FStar_Tactics_Builtins.intro))
      (fun uu___1 ->
         (fun uu___1 ->
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Range.mk_range "FStar.Tactics.Logic.fst"
                    (Prims.of_int (323)) (Prims.of_int (12))
                    (Prims.of_int (323)) (Prims.of_int (67)))
                 (FStar_Range.mk_range "FStar.Tactics.Logic.fst"
                    (Prims.of_int (324)) (Prims.of_int (4))
                    (Prims.of_int (324)) (Prims.of_int (10)))
                 (Obj.magic
                    (FStar_Tactics_Derived.trytac
                       (fun uu___2 ->
                          FStar_Tactics_Effect.tac_bind
                            (FStar_Range.mk_range "FStar.Tactics.Logic.fst"
                               (Prims.of_int (323)) (Prims.of_int (30))
                               (Prims.of_int (323)) (Prims.of_int (56)))
                            (FStar_Range.mk_range "FStar.Tactics.Logic.fst"
                               (Prims.of_int (323)) (Prims.of_int (58))
                               (Prims.of_int (323)) (Prims.of_int (66)))
                            (Obj.magic
                               (FStar_Tactics_Derived.apply
                                  (FStar_Reflection_Builtins.pack_ln
                                     (FStar_Reflection_Data.Tv_FVar
                                        (FStar_Reflection_Builtins.pack_fv
                                           ["FStar";
                                           "Tactics";
                                           "Logic";
                                           "lemma_from_squash"])))))
                            (fun uu___3 ->
                               (fun uu___3 ->
                                  Obj.magic (FStar_Tactics_Builtins.intro ()))
                                 uu___3))))
                 (fun uu___2 ->
                    (fun uu___2 -> Obj.magic (FStar_Tactics_Derived.smt ()))
                      uu___2))) uu___1)
let easy : 'a . 'a -> 'a = fun x -> x
let (using_lemma :
  FStar_Reflection_Types.term ->
    (FStar_Reflection_Types.binder, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    FStar_Tactics_Derived.try_with
      (fun uu___ ->
         match () with
         | () ->
             pose_lemma
               (FStar_Reflection_Builtins.pack_ln
                  (FStar_Reflection_Data.Tv_App
                     ((FStar_Reflection_Builtins.pack_ln
                         (FStar_Reflection_Data.Tv_FVar
                            (FStar_Reflection_Builtins.pack_fv
                               ["FStar"; "Tactics"; "Logic"; "lem1_fa"]))),
                       (t, FStar_Reflection_Data.Q_Explicit)))))
      (fun uu___ ->
         FStar_Tactics_Derived.try_with
           (fun uu___1 ->
              match () with
              | () ->
                  pose_lemma
                    (FStar_Reflection_Builtins.pack_ln
                       (FStar_Reflection_Data.Tv_App
                          ((FStar_Reflection_Builtins.pack_ln
                              (FStar_Reflection_Data.Tv_FVar
                                 (FStar_Reflection_Builtins.pack_fv
                                    ["FStar"; "Tactics"; "Logic"; "lem2_fa"]))),
                            (t, FStar_Reflection_Data.Q_Explicit)))))
           (fun uu___1 ->
              FStar_Tactics_Derived.try_with
                (fun uu___2 ->
                   match () with
                   | () ->
                       pose_lemma
                         (FStar_Reflection_Builtins.pack_ln
                            (FStar_Reflection_Data.Tv_App
                               ((FStar_Reflection_Builtins.pack_ln
                                   (FStar_Reflection_Data.Tv_FVar
                                      (FStar_Reflection_Builtins.pack_fv
                                         ["FStar";
                                         "Tactics";
                                         "Logic";
                                         "lem3_fa"]))),
                                 (t, FStar_Reflection_Data.Q_Explicit)))))
                (fun uu___2 ->
                   (fun uu___2 ->
                      Obj.magic
                        (FStar_Tactics_Derived.fail
                           "using_lemma: failed to instantiate")) uu___2)))