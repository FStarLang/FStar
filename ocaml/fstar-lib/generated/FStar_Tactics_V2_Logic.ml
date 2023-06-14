open Prims
let (cur_formula :
  unit ->
    (FStar_Reflection_V2_Formula.formula, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
               (Prims.of_int (28)) (Prims.of_int (51)) (Prims.of_int (28))
               (Prims.of_int (64)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
               (Prims.of_int (28)) (Prims.of_int (35)) (Prims.of_int (28))
               (Prims.of_int (64)))))
      (Obj.magic (FStar_Tactics_V2_Derived.cur_goal ()))
      (fun uu___1 ->
         (fun uu___1 ->
            Obj.magic (FStar_Reflection_V2_Formula.term_as_formula uu___1))
           uu___1)
let (l_revert : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
               (Prims.of_int (37)) (Prims.of_int (4)) (Prims.of_int (37))
               (Prims.of_int (13)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
               (Prims.of_int (38)) (Prims.of_int (4)) (Prims.of_int (38))
               (Prims.of_int (26)))))
      (Obj.magic (FStar_Tactics_V2_Builtins.revert ()))
      (fun uu___1 ->
         (fun uu___1 ->
            Obj.magic
              (FStar_Tactics_V2_Derived.apply
                 (FStar_Reflection_V2_Builtins.pack_ln
                    (FStar_Reflection_V2_Data.Tv_FVar
                       (FStar_Reflection_V2_Builtins.pack_fv
                          ["FStar";
                          "Tactics";
                          "V2";
                          "Logic";
                          "revert_squash"]))))) uu___1)
let rec (l_revert_all :
  FStar_Tactics_NamedView.binding Prims.list ->
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
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
                            (Prims.of_int (44)) (Prims.of_int (21))
                            (Prims.of_int (44)) (Prims.of_int (32)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
                            (Prims.of_int (44)) (Prims.of_int (34))
                            (Prims.of_int (44)) (Prims.of_int (49)))))
                   (Obj.magic (l_revert ()))
                   (fun uu___1 ->
                      (fun uu___1 -> Obj.magic (l_revert_all tl)) uu___1))))
      uu___
let (forall_intro :
  unit ->
    (FStar_Tactics_NamedView.binding, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
               (Prims.of_int (52)) (Prims.of_int (4)) (Prims.of_int (52))
               (Prims.of_int (31)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
               (Prims.of_int (53)) (Prims.of_int (4)) (Prims.of_int (53))
               (Prims.of_int (12)))))
      (Obj.magic
         (FStar_Tactics_V2_Derived.apply_lemma
            (FStar_Reflection_V2_Builtins.pack_ln
               (FStar_Reflection_V2_Data.Tv_FVar
                  (FStar_Reflection_V2_Builtins.pack_fv
                     ["FStar"; "Tactics"; "V2"; "Logic"; "fa_intro_lem"])))))
      (fun uu___1 ->
         (fun uu___1 -> Obj.magic (FStar_Tactics_V2_Builtins.intro ()))
           uu___1)
let (forall_intro_as :
  Prims.string ->
    (FStar_Tactics_NamedView.binding, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun s ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
               (Prims.of_int (57)) (Prims.of_int (4)) (Prims.of_int (57))
               (Prims.of_int (31)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
               (Prims.of_int (58)) (Prims.of_int (4)) (Prims.of_int (58))
               (Prims.of_int (14)))))
      (Obj.magic
         (FStar_Tactics_V2_Derived.apply_lemma
            (FStar_Reflection_V2_Builtins.pack_ln
               (FStar_Reflection_V2_Data.Tv_FVar
                  (FStar_Reflection_V2_Builtins.pack_fv
                     ["FStar"; "Tactics"; "V2"; "Logic"; "fa_intro_lem"])))))
      (fun uu___ ->
         (fun uu___ -> Obj.magic (FStar_Tactics_V2_Derived.intro_as s)) uu___)
let (forall_intros :
  unit ->
    (FStar_Tactics_NamedView.binding Prims.list, unit)
      FStar_Tactics_Effect.tac_repr)
  = fun uu___ -> FStar_Tactics_V2_Derived.repeat1 forall_intro
let (split : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_V2_Derived.try_with
      (fun uu___1 ->
         match () with
         | () ->
             FStar_Tactics_V2_Derived.apply_lemma
               (FStar_Reflection_V2_Builtins.pack_ln
                  (FStar_Reflection_V2_Data.Tv_FVar
                     (FStar_Reflection_V2_Builtins.pack_fv
                        ["FStar"; "Tactics"; "V2"; "Logic"; "split_lem"]))))
      (fun uu___1 ->
         (fun uu___1 ->
            Obj.magic (FStar_Tactics_V2_Derived.fail "Could not split goal"))
           uu___1)
let (implies_intro :
  unit ->
    (FStar_Tactics_NamedView.binding, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
               (Prims.of_int (80)) (Prims.of_int (4)) (Prims.of_int (80))
               (Prims.of_int (32)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
               (Prims.of_int (81)) (Prims.of_int (4)) (Prims.of_int (81))
               (Prims.of_int (12)))))
      (Obj.magic
         (FStar_Tactics_V2_Derived.apply_lemma
            (FStar_Reflection_V2_Builtins.pack_ln
               (FStar_Reflection_V2_Data.Tv_FVar
                  (FStar_Reflection_V2_Builtins.pack_fv
                     ["FStar"; "Tactics"; "V2"; "Logic"; "imp_intro_lem"])))))
      (fun uu___1 ->
         (fun uu___1 -> Obj.magic (FStar_Tactics_V2_Builtins.intro ()))
           uu___1)
let (implies_intro_as :
  Prims.string ->
    (FStar_Tactics_NamedView.binding, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun s ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
               (Prims.of_int (84)) (Prims.of_int (4)) (Prims.of_int (84))
               (Prims.of_int (32)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
               (Prims.of_int (85)) (Prims.of_int (4)) (Prims.of_int (85))
               (Prims.of_int (14)))))
      (Obj.magic
         (FStar_Tactics_V2_Derived.apply_lemma
            (FStar_Reflection_V2_Builtins.pack_ln
               (FStar_Reflection_V2_Data.Tv_FVar
                  (FStar_Reflection_V2_Builtins.pack_fv
                     ["FStar"; "Tactics"; "V2"; "Logic"; "imp_intro_lem"])))))
      (fun uu___ ->
         (fun uu___ -> Obj.magic (FStar_Tactics_V2_Derived.intro_as s)) uu___)
let (implies_intros :
  unit ->
    (FStar_Tactics_NamedView.binding Prims.list, unit)
      FStar_Tactics_Effect.tac_repr)
  = fun uu___ -> FStar_Tactics_V2_Derived.repeat1 implies_intro
let (l_intro :
  unit ->
    (FStar_Tactics_NamedView.binding, unit) FStar_Tactics_Effect.tac_repr)
  = fun uu___ -> FStar_Tactics_V2_Derived.or_else forall_intro implies_intro
let (l_intros :
  unit ->
    (FStar_Tactics_NamedView.binding Prims.list, unit)
      FStar_Tactics_Effect.tac_repr)
  = fun uu___ -> FStar_Tactics_V2_Derived.repeat l_intro
let (squash_intro : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_V2_Derived.apply
      (FStar_Reflection_V2_Builtins.pack_ln
         (FStar_Reflection_V2_Data.Tv_FVar
            (FStar_Reflection_V2_Builtins.pack_fv
               ["FStar"; "Squash"; "return_squash"])))
let (l_exact :
  FStar_Tactics_NamedView.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    FStar_Tactics_V2_Derived.try_with
      (fun uu___ -> match () with | () -> FStar_Tactics_V2_Derived.exact t)
      (fun uu___ ->
         FStar_Tactics_Effect.tac_bind
           (FStar_Sealed.seal
              (Obj.magic
                 (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
                    (Prims.of_int (101)) (Prims.of_int (12))
                    (Prims.of_int (101)) (Prims.of_int (27)))))
           (FStar_Sealed.seal
              (Obj.magic
                 (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
                    (Prims.of_int (101)) (Prims.of_int (29))
                    (Prims.of_int (101)) (Prims.of_int (36)))))
           (Obj.magic (squash_intro ()))
           (fun uu___1 ->
              (fun uu___1 -> Obj.magic (FStar_Tactics_V2_Derived.exact t))
                uu___1))
let (hyp :
  FStar_Tactics_NamedView.namedv ->
    (unit, unit) FStar_Tactics_Effect.tac_repr)
  = fun x -> l_exact (FStar_Tactics_V2_SyntaxCoercions.namedv_to_term x)
let (pose_lemma :
  FStar_Tactics_NamedView.term ->
    (FStar_Tactics_NamedView.binding, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
               (Prims.of_int (112)) (Prims.of_int (10)) (Prims.of_int (112))
               (Prims.of_int (28)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
               (Prims.of_int (112)) (Prims.of_int (31)) (Prims.of_int (130))
               (Prims.of_int (5)))))
      (Obj.magic
         (FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
                     (Prims.of_int (112)) (Prims.of_int (14))
                     (Prims.of_int (112)) (Prims.of_int (26)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
                     (Prims.of_int (112)) (Prims.of_int (10))
                     (Prims.of_int (112)) (Prims.of_int (28)))))
            (Obj.magic (FStar_Tactics_V2_Derived.cur_env ()))
            (fun uu___ ->
               (fun uu___ -> Obj.magic (FStar_Tactics_NamedView.tcc uu___ t))
                 uu___)))
      (fun uu___ ->
         (fun c ->
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
                          (Prims.of_int (114)) (Prims.of_int (4))
                          (Prims.of_int (116)) (Prims.of_int (18)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
                          (Prims.of_int (112)) (Prims.of_int (31))
                          (Prims.of_int (130)) (Prims.of_int (5)))))
                 (match c with
                  | FStar_Reflection_V2_Data.C_Lemma (pre, post, uu___) ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___1 -> (pre, post))
                  | uu___ -> FStar_Tactics_V2_Derived.fail "")
                 (fun uu___ ->
                    (fun uu___ ->
                       match uu___ with
                       | (pre, post) ->
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.V2.Logic.fst"
                                         (Prims.of_int (118))
                                         (Prims.of_int (13))
                                         (Prims.of_int (118))
                                         (Prims.of_int (27)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.V2.Logic.fst"
                                         (Prims.of_int (118))
                                         (Prims.of_int (30))
                                         (Prims.of_int (130))
                                         (Prims.of_int (5)))))
                                (FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___1 ->
                                      FStar_Reflection_V2_Builtins.pack_ln
                                        (FStar_Reflection_V2_Data.Tv_App
                                           (post,
                                             ((FStar_Reflection_V2_Builtins.pack_ln
                                                 (FStar_Reflection_V2_Data.Tv_Const
                                                    FStar_Reflection_V2_Data.C_Unit)),
                                               FStar_Reflection_V2_Data.Q_Explicit)))))
                                (fun uu___1 ->
                                   (fun post1 ->
                                      Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "FStar.Tactics.V2.Logic.fst"
                                                    (Prims.of_int (119))
                                                    (Prims.of_int (13))
                                                    (Prims.of_int (119))
                                                    (Prims.of_int (30)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "FStar.Tactics.V2.Logic.fst"
                                                    (Prims.of_int (121))
                                                    (Prims.of_int (2))
                                                    (Prims.of_int (130))
                                                    (Prims.of_int (5)))))
                                           (Obj.magic
                                              (FStar_Tactics_V2_Derived.norm_term
                                                 [] post1))
                                           (fun uu___1 ->
                                              (fun post2 ->
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "FStar.Tactics.V2.Logic.fst"
                                                               (Prims.of_int (121))
                                                               (Prims.of_int (8))
                                                               (Prims.of_int (121))
                                                               (Prims.of_int (28)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "FStar.Tactics.V2.Logic.fst"
                                                               (Prims.of_int (121))
                                                               (Prims.of_int (2))
                                                               (Prims.of_int (130))
                                                               (Prims.of_int (5)))))
                                                      (Obj.magic
                                                         (FStar_Reflection_V2_Formula.term_as_formula'
                                                            pre))
                                                      (fun uu___1 ->
                                                         (fun uu___1 ->
                                                            match uu___1 with
                                                            | FStar_Reflection_V2_Formula.True_
                                                                ->
                                                                Obj.magic
                                                                  (FStar_Tactics_V2_Derived.pose
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_App
                                                                    ((FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_App
                                                                    ((FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_App
                                                                    ((FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_App
                                                                    ((FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "V2";
                                                                    "Logic";
                                                                    "__lemma_to_squash"]))),
                                                                    (pre,
                                                                    FStar_Reflection_V2_Data.Q_Implicit)))),
                                                                    (post2,
                                                                    FStar_Reflection_V2_Data.Q_Implicit)))),
                                                                    ((FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_Const
                                                                    FStar_Reflection_V2_Data.C_Unit)),
                                                                    FStar_Reflection_V2_Data.Q_Explicit)))),
                                                                    ((FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_Abs
                                                                    ((FStar_Reflection_V2_Builtins.pack_binder
                                                                    {
                                                                    FStar_Reflection_V2_Data.sort2
                                                                    =
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["Prims";
                                                                    "unit"])));
                                                                    FStar_Reflection_V2_Data.qual
                                                                    =
                                                                    FStar_Reflection_V2_Data.Q_Explicit;
                                                                    FStar_Reflection_V2_Data.attrs
                                                                    = [];
                                                                    FStar_Reflection_V2_Data.ppname2
                                                                    =
                                                                    (FStar_Sealed.seal
                                                                    "uu___")
                                                                    }), t))),
                                                                    FStar_Reflection_V2_Data.Q_Explicit)))))
                                                            | uu___2 ->
                                                                Obj.magic
                                                                  (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Logic.fst"
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (37)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Logic.fst"
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (130))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Derived.tcut
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_App
                                                                    ((FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["Prims";
                                                                    "squash"]))),
                                                                    (pre,
                                                                    FStar_Reflection_V2_Data.Q_Explicit))))))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun reqb
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Logic.fst"
                                                                    (Prims.of_int (127))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (127))
                                                                    (Prims.of_int (95)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Logic.fst"
                                                                    (Prims.of_int (128))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (130))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Derived.pose
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_App
                                                                    ((FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_App
                                                                    ((FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_App
                                                                    ((FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_App
                                                                    ((FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "V2";
                                                                    "Logic";
                                                                    "__lemma_to_squash"]))),
                                                                    (pre,
                                                                    FStar_Reflection_V2_Data.Q_Implicit)))),
                                                                    (post2,
                                                                    FStar_Reflection_V2_Data.Q_Implicit)))),
                                                                    ((FStar_Tactics_V2_SyntaxCoercions.binding_to_term
                                                                    reqb),
                                                                    FStar_Reflection_V2_Data.Q_Explicit)))),
                                                                    ((FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_Abs
                                                                    ((FStar_Reflection_V2_Builtins.pack_binder
                                                                    {
                                                                    FStar_Reflection_V2_Data.sort2
                                                                    =
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["Prims";
                                                                    "unit"])));
                                                                    FStar_Reflection_V2_Data.qual
                                                                    =
                                                                    FStar_Reflection_V2_Data.Q_Explicit;
                                                                    FStar_Reflection_V2_Data.attrs
                                                                    = [];
                                                                    FStar_Reflection_V2_Data.ppname2
                                                                    =
                                                                    (FStar_Sealed.seal
                                                                    "uu___")
                                                                    }), t))),
                                                                    FStar_Reflection_V2_Data.Q_Explicit))))))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun b ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Logic.fst"
                                                                    (Prims.of_int (128))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (128))
                                                                    (Prims.of_int (11)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Logic.fst"
                                                                    (Prims.of_int (129))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (130))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Derived.flip
                                                                    ()))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Logic.fst"
                                                                    (Prims.of_int (129))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (129))
                                                                    (Prims.of_int (27)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Logic.fst"
                                                                    (Prims.of_int (127))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (127))
                                                                    (Prims.of_int (9)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Logic.fst"
                                                                    (Prims.of_int (129))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (129))
                                                                    (Prims.of_int (27)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Logic.fst"
                                                                    (Prims.of_int (129))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (129))
                                                                    (Prims.of_int (27)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Derived.trytac
                                                                    FStar_Tactics_V2_Derived.trivial))
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
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
               (Prims.of_int (133)) (Prims.of_int (11)) (Prims.of_int (135))
               (Prims.of_int (64)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
               (Prims.of_int (133)) (Prims.of_int (4)) (Prims.of_int (135))
               (Prims.of_int (64)))))
      (Obj.magic
         (FStar_Tactics_V2_Derived.repeatseq
            (fun uu___1 ->
               FStar_Tactics_V2_Derived.first
                 [(fun uu___2 ->
                     FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.V2.Logic.fst"
                                (Prims.of_int (134)) (Prims.of_int (50))
                                (Prims.of_int (134)) (Prims.of_int (62)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.V2.Logic.fst"
                                (Prims.of_int (134)) (Prims.of_int (43))
                                (Prims.of_int (134)) (Prims.of_int (62)))))
                       (Obj.magic (l_intro ()))
                       (fun uu___3 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___4 -> ())));
                 (fun uu___2 ->
                    FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range
                               "FStar.Tactics.V2.Logic.fst"
                               (Prims.of_int (135)) (Prims.of_int (50))
                               (Prims.of_int (135)) (Prims.of_int (60)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range
                               "FStar.Tactics.V2.Logic.fst"
                               (Prims.of_int (135)) (Prims.of_int (43))
                               (Prims.of_int (135)) (Prims.of_int (60)))))
                      (Obj.magic (split ()))
                      (fun uu___3 ->
                         FStar_Tactics_Effect.lift_div_tac (fun uu___4 -> ())))])))
      (fun uu___1 -> FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> ()))
let rec (visit :
  (unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) ->
    (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun callback ->
    FStar_Tactics_V2_Derived.focus
      (fun uu___ ->
         FStar_Tactics_V2_Derived.or_else callback
           (fun uu___1 ->
              FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
                         (Prims.of_int (141)) (Prims.of_int (28))
                         (Prims.of_int (141)) (Prims.of_int (39)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
                         (Prims.of_int (142)) (Prims.of_int (20))
                         (Prims.of_int (152)) (Prims.of_int (26)))))
                (Obj.magic (FStar_Tactics_V2_Derived.cur_goal ()))
                (fun uu___2 ->
                   (fun g ->
                      Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "FStar.Tactics.V2.Logic.fst"
                                    (Prims.of_int (142)) (Prims.of_int (26))
                                    (Prims.of_int (142)) (Prims.of_int (43)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "FStar.Tactics.V2.Logic.fst"
                                    (Prims.of_int (142)) (Prims.of_int (20))
                                    (Prims.of_int (152)) (Prims.of_int (26)))))
                           (Obj.magic
                              (FStar_Reflection_V2_Formula.term_as_formula g))
                           (fun uu___2 ->
                              (fun uu___2 ->
                                 match uu___2 with
                                 | FStar_Reflection_V2_Formula.Forall
                                     (_b, _sort, _phi) ->
                                     Obj.magic
                                       (Obj.repr
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "FStar.Tactics.V2.Logic.fst"
                                                      (Prims.of_int (144))
                                                      (Prims.of_int (38))
                                                      (Prims.of_int (144))
                                                      (Prims.of_int (54)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "FStar.Tactics.V2.Logic.fst"
                                                      (Prims.of_int (145))
                                                      (Prims.of_int (24))
                                                      (Prims.of_int (145))
                                                      (Prims.of_int (87)))))
                                             (Obj.magic (forall_intros ()))
                                             (fun uu___3 ->
                                                (fun binders ->
                                                   Obj.magic
                                                     (FStar_Tactics_V2_Derived.seq
                                                        (fun uu___3 ->
                                                           visit callback)
                                                        (fun uu___3 ->
                                                           l_revert_all
                                                             binders)))
                                                  uu___3)))
                                 | FStar_Reflection_V2_Formula.And (p, q) ->
                                     Obj.magic
                                       (Obj.repr
                                          (FStar_Tactics_V2_Derived.seq split
                                             (fun uu___3 -> visit callback)))
                                 | FStar_Reflection_V2_Formula.Implies 
                                     (p, q) ->
                                     Obj.magic
                                       (Obj.repr
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "FStar.Tactics.V2.Logic.fst"
                                                      (Prims.of_int (149))
                                                      (Prims.of_int (32))
                                                      (Prims.of_int (149))
                                                      (Prims.of_int (48)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "FStar.Tactics.V2.Logic.fst"
                                                      (Prims.of_int (150))
                                                      (Prims.of_int (24))
                                                      (Prims.of_int (150))
                                                      (Prims.of_int (63)))))
                                             (Obj.magic (implies_intro ()))
                                             (fun uu___3 ->
                                                (fun uu___3 ->
                                                   Obj.magic
                                                     (FStar_Tactics_V2_Derived.seq
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
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
               (Prims.of_int (157)) (Prims.of_int (12)) (Prims.of_int (157))
               (Prims.of_int (22)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
               (Prims.of_int (157)) (Prims.of_int (25)) (Prims.of_int (167))
               (Prims.of_int (37)))))
      (Obj.magic (FStar_Tactics_V2_Derived.cur_env ()))
      (fun uu___1 ->
         (fun e ->
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
                          (Prims.of_int (158)) (Prims.of_int (12))
                          (Prims.of_int (158)) (Prims.of_int (23)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
                          (Prims.of_int (158)) (Prims.of_int (26))
                          (Prims.of_int (167)) (Prims.of_int (37)))))
                 (Obj.magic (FStar_Tactics_V2_Derived.cur_goal ()))
                 (fun uu___1 ->
                    (fun g ->
                       Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.V2.Logic.fst"
                                     (Prims.of_int (159)) (Prims.of_int (12))
                                     (Prims.of_int (159)) (Prims.of_int (43)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.V2.Logic.fst"
                                     (Prims.of_int (160)) (Prims.of_int (4))
                                     (Prims.of_int (167)) (Prims.of_int (37)))))
                            (Obj.magic
                               (FStar_Tactics_V2_Derived.destruct_equality_implication
                                  g))
                            (fun uu___1 ->
                               (fun r ->
                                  match r with
                                  | FStar_Pervasives_Native.None ->
                                      Obj.magic
                                        (Obj.repr
                                           (FStar_Tactics_V2_Derived.fail
                                              "Not an equality implication"))
                                  | FStar_Pervasives_Native.Some
                                      (uu___1, rhs) ->
                                      Obj.magic
                                        (Obj.repr
                                           (FStar_Tactics_Effect.tac_bind
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "FStar.Tactics.V2.Logic.fst"
                                                       (Prims.of_int (164))
                                                       (Prims.of_int (19))
                                                       (Prims.of_int (164))
                                                       (Prims.of_int (35)))))
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "FStar.Tactics.V2.Logic.fst"
                                                       (Prims.of_int (165))
                                                       (Prims.of_int (8))
                                                       (Prims.of_int (167))
                                                       (Prims.of_int (37)))))
                                              (Obj.magic (implies_intro ()))
                                              (fun uu___2 ->
                                                 (fun eq_h ->
                                                    Obj.magic
                                                      (FStar_Tactics_Effect.tac_bind
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "FStar.Tactics.V2.Logic.fst"
                                                                  (Prims.of_int (165))
                                                                  (Prims.of_int (8))
                                                                  (Prims.of_int (165))
                                                                  (Prims.of_int (20)))))
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "FStar.Tactics.V2.Logic.fst"
                                                                  (Prims.of_int (166))
                                                                  (Prims.of_int (8))
                                                                  (Prims.of_int (167))
                                                                  (Prims.of_int (37)))))
                                                         (Obj.magic
                                                            (FStar_Tactics_V2_Builtins.rewrite
                                                               eq_h))
                                                         (fun uu___2 ->
                                                            (fun uu___2 ->
                                                               Obj.magic
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Logic.fst"
                                                                    (Prims.of_int (166))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (166))
                                                                    (Prims.of_int (20)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Logic.fst"
                                                                    (Prims.of_int (167))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (167))
                                                                    (Prims.of_int (37)))))
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.clear_top
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
  FStar_Tactics_NamedView.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun tm ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
               (Prims.of_int (173)) (Prims.of_int (12)) (Prims.of_int (173))
               (Prims.of_int (23)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
               (Prims.of_int (174)) (Prims.of_int (4)) (Prims.of_int (188))
               (Prims.of_int (11)))))
      (Obj.magic (FStar_Tactics_V2_Derived.cur_goal ()))
      (fun uu___ ->
         (fun g ->
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
                          (Prims.of_int (174)) (Prims.of_int (10))
                          (Prims.of_int (174)) (Prims.of_int (27)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
                          (Prims.of_int (174)) (Prims.of_int (4))
                          (Prims.of_int (188)) (Prims.of_int (11)))))
                 (Obj.magic (FStar_Reflection_V2_Formula.term_as_formula g))
                 (fun uu___ ->
                    (fun uu___ ->
                       match uu___ with
                       | FStar_Reflection_V2_Formula.App (hd, arg) ->
                           Obj.magic
                             (Obj.repr
                                (if
                                   FStar_Reflection_V2_Builtins.term_eq hd tm
                                 then
                                   Obj.repr
                                     (FStar_Tactics_V2_Derived.trivial ())
                                 else
                                   Obj.repr
                                     (FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___2 -> ()))))
                       | uu___1 ->
                           Obj.magic
                             (Obj.repr
                                (FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "FStar.Tactics.V2.Logic.fst"
                                            (Prims.of_int (180))
                                            (Prims.of_int (16))
                                            (Prims.of_int (180))
                                            (Prims.of_int (47)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "FStar.Tactics.V2.Logic.fst"
                                            (Prims.of_int (181))
                                            (Prims.of_int (8))
                                            (Prims.of_int (187))
                                            (Prims.of_int (66)))))
                                   (Obj.magic
                                      (FStar_Tactics_V2_Derived.destruct_equality_implication
                                         g))
                                   (fun uu___2 ->
                                      (fun r ->
                                         match r with
                                         | FStar_Pervasives_Native.None ->
                                             Obj.magic
                                               (Obj.repr
                                                  (FStar_Tactics_V2_Derived.fail
                                                     "Not an equality implication"))
                                         | FStar_Pervasives_Native.Some
                                             (uu___2, rhs) ->
                                             Obj.magic
                                               (Obj.repr
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "FStar.Tactics.V2.Logic.fst"
                                                              (Prims.of_int (184))
                                                              (Prims.of_int (23))
                                                              (Prims.of_int (184))
                                                              (Prims.of_int (39)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "FStar.Tactics.V2.Logic.fst"
                                                              (Prims.of_int (185))
                                                              (Prims.of_int (12))
                                                              (Prims.of_int (187))
                                                              (Prims.of_int (66)))))
                                                     (Obj.magic
                                                        (implies_intro ()))
                                                     (fun uu___3 ->
                                                        (fun eq_h ->
                                                           Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Logic.fst"
                                                                    (Prims.of_int (185))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (185))
                                                                    (Prims.of_int (24)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Logic.fst"
                                                                    (Prims.of_int (186))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (187))
                                                                    (Prims.of_int (66)))))
                                                                (Obj.magic
                                                                   (FStar_Tactics_V2_Builtins.rewrite
                                                                    eq_h))
                                                                (fun uu___3
                                                                   ->
                                                                   (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Logic.fst"
                                                                    (Prims.of_int (186))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (186))
                                                                    (Prims.of_int (24)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Logic.fst"
                                                                    (Prims.of_int (187))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (187))
                                                                    (Prims.of_int (66)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V2_Builtins.clear_top
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
  FStar_Tactics_NamedView.term ->
    (FStar_Tactics_NamedView.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
               (Prims.of_int (206)) (Prims.of_int (12)) (Prims.of_int (206))
               (Prims.of_int (18)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
               (Prims.of_int (207)) (Prims.of_int (4)) (Prims.of_int (209))
               (Prims.of_int (19)))))
      (FStar_Tactics_Effect.lift_div_tac
         (fun uu___ ->
            FStar_Reflection_V2_Builtins.pack_ln
              (FStar_Reflection_V2_Data.Tv_FVar
                 (FStar_Reflection_V2_Builtins.pack_fv
                    ["FStar"; "Tactics"; "V2"; "Logic"; "vbind"]))))
      (fun uu___ ->
         (fun v ->
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
                          (Prims.of_int (207)) (Prims.of_int (4))
                          (Prims.of_int (207)) (Prims.of_int (32)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
                          (Prims.of_int (207)) (Prims.of_int (33))
                          (Prims.of_int (209)) (Prims.of_int (19)))))
                 (Obj.magic
                    (FStar_Tactics_V2_Derived.apply_lemma
                       (FStar_Reflection_V2_Derived.mk_e_app v [t])))
                 (fun uu___ ->
                    (fun uu___ ->
                       Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.V2.Logic.fst"
                                     (Prims.of_int (208)) (Prims.of_int (12))
                                     (Prims.of_int (208)) (Prims.of_int (20)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range " dummy"
                                     Prims.int_zero Prims.int_zero
                                     Prims.int_zero Prims.int_zero)))
                            (Obj.magic (FStar_Tactics_V2_Builtins.intro ()))
                            (fun b ->
                               FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___1 ->
                                    FStar_Tactics_NamedView.pack
                                      (FStar_Tactics_NamedView.Tv_Var
                                         (FStar_Tactics_V2_SyntaxCoercions.binding_to_namedv
                                            b)))))) uu___))) uu___)
let (cases_or :
  FStar_Tactics_NamedView.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun o ->
    FStar_Tactics_V2_Derived.apply_lemma
      (FStar_Reflection_V2_Derived.mk_e_app
         (FStar_Reflection_V2_Builtins.pack_ln
            (FStar_Reflection_V2_Data.Tv_FVar
               (FStar_Reflection_V2_Builtins.pack_fv
                  ["FStar"; "Tactics"; "V2"; "Logic"; "or_ind"]))) [o])
let (cases_bool :
  FStar_Tactics_NamedView.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun b ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
               (Prims.of_int (227)) (Prims.of_int (13)) (Prims.of_int (227))
               (Prims.of_int (22)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
               (Prims.of_int (228)) (Prims.of_int (4)) (Prims.of_int (229))
               (Prims.of_int (104)))))
      (FStar_Tactics_Effect.lift_div_tac
         (fun uu___ ->
            FStar_Reflection_V2_Builtins.pack_ln
              (FStar_Reflection_V2_Data.Tv_FVar
                 (FStar_Reflection_V2_Builtins.pack_fv
                    ["FStar"; "Tactics"; "V2"; "Logic"; "bool_ind"]))))
      (fun uu___ ->
         (fun bi ->
            Obj.magic
              (FStar_Tactics_V2_Derived.seq
                 (fun uu___ ->
                    FStar_Tactics_V2_Derived.apply_lemma
                      (FStar_Reflection_V2_Derived.mk_e_app bi [b]))
                 (fun uu___ ->
                    FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range
                               "FStar.Tactics.V2.Logic.fst"
                               (Prims.of_int (229)) (Prims.of_int (27))
                               (Prims.of_int (229)) (Prims.of_int (97)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range
                               "FStar.Tactics.V2.Logic.fst"
                               (Prims.of_int (229)) (Prims.of_int (101))
                               (Prims.of_int (229)) (Prims.of_int (103)))))
                      (Obj.magic
                         (FStar_Tactics_V2_Derived.trytac
                            (fun uu___1 ->
                               FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "FStar.Tactics.V2.Logic.fst"
                                          (Prims.of_int (229))
                                          (Prims.of_int (53))
                                          (Prims.of_int (229))
                                          (Prims.of_int (69)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "FStar.Tactics.V2.Logic.fst"
                                          (Prims.of_int (229))
                                          (Prims.of_int (73))
                                          (Prims.of_int (229))
                                          (Prims.of_int (96)))))
                                 (Obj.magic (implies_intro ()))
                                 (fun uu___2 ->
                                    (fun b1 ->
                                       Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "FStar.Tactics.V2.Logic.fst"
                                                     (Prims.of_int (229))
                                                     (Prims.of_int (73))
                                                     (Prims.of_int (229))
                                                     (Prims.of_int (82)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "FStar.Tactics.V2.Logic.fst"
                                                     (Prims.of_int (229))
                                                     (Prims.of_int (84))
                                                     (Prims.of_int (229))
                                                     (Prims.of_int (96)))))
                                            (Obj.magic
                                               (FStar_Tactics_V2_Builtins.rewrite
                                                  b1))
                                            (fun uu___2 ->
                                               (fun uu___2 ->
                                                  Obj.magic
                                                    (FStar_Tactics_V2_Builtins.clear_top
                                                       ())) uu___2))) uu___2))))
                      (fun uu___1 ->
                         FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> ())))))
           uu___)
let (left : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_V2_Derived.apply_lemma
      (FStar_Reflection_V2_Builtins.pack_ln
         (FStar_Reflection_V2_Data.Tv_FVar
            (FStar_Reflection_V2_Builtins.pack_fv
               ["FStar"; "Tactics"; "V2"; "Logic"; "or_intro_1"])))
let (right : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_V2_Derived.apply_lemma
      (FStar_Reflection_V2_Builtins.pack_ln
         (FStar_Reflection_V2_Data.Tv_FVar
            (FStar_Reflection_V2_Builtins.pack_fv
               ["FStar"; "Tactics"; "V2"; "Logic"; "or_intro_2"])))
let (and_elim :
  FStar_Tactics_NamedView.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    FStar_Tactics_V2_Derived.try_with
      (fun uu___ ->
         match () with
         | () ->
             FStar_Tactics_V2_Derived.apply_lemma
               (FStar_Reflection_V2_Builtins.pack_ln
                  (FStar_Reflection_V2_Data.Tv_App
                     ((FStar_Reflection_V2_Builtins.pack_ln
                         (FStar_Reflection_V2_Data.Tv_FVar
                            (FStar_Reflection_V2_Builtins.pack_fv
                               ["FStar";
                               "Tactics";
                               "V2";
                               "Logic";
                               "__and_elim"]))),
                       (t, FStar_Reflection_V2_Data.Q_Explicit)))))
      (fun uu___ ->
         FStar_Tactics_V2_Derived.apply_lemma
           (FStar_Reflection_V2_Builtins.pack_ln
              (FStar_Reflection_V2_Data.Tv_App
                 ((FStar_Reflection_V2_Builtins.pack_ln
                     (FStar_Reflection_V2_Data.Tv_FVar
                        (FStar_Reflection_V2_Builtins.pack_fv
                           ["FStar"; "Tactics"; "V2"; "Logic"; "__and_elim'"]))),
                   (t, FStar_Reflection_V2_Data.Q_Explicit)))))
let (destruct_and :
  FStar_Tactics_NamedView.term ->
    ((FStar_Tactics_NamedView.binding * FStar_Tactics_NamedView.binding),
      unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
               (Prims.of_int (262)) (Prims.of_int (4)) (Prims.of_int (262))
               (Prims.of_int (14)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
               (Prims.of_int (263)) (Prims.of_int (4)) (Prims.of_int (263))
               (Prims.of_int (40))))) (Obj.magic (and_elim t))
      (fun uu___ ->
         (fun uu___ ->
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
                          (Prims.of_int (263)) (Prims.of_int (5))
                          (Prims.of_int (263)) (Prims.of_int (21)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
                          (Prims.of_int (263)) (Prims.of_int (4))
                          (Prims.of_int (263)) (Prims.of_int (40)))))
                 (Obj.magic (implies_intro ()))
                 (fun uu___1 ->
                    (fun uu___1 ->
                       Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.V2.Logic.fst"
                                     (Prims.of_int (263)) (Prims.of_int (23))
                                     (Prims.of_int (263)) (Prims.of_int (39)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.V2.Logic.fst"
                                     (Prims.of_int (263)) (Prims.of_int (4))
                                     (Prims.of_int (263)) (Prims.of_int (40)))))
                            (Obj.magic (implies_intro ()))
                            (fun uu___2 ->
                               FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___3 -> (uu___1, uu___2))))) uu___1)))
           uu___)
let (witness :
  FStar_Tactics_NamedView.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
               (Prims.of_int (269)) (Prims.of_int (4)) (Prims.of_int (269))
               (Prims.of_int (26)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
               (Prims.of_int (270)) (Prims.of_int (4)) (Prims.of_int (270))
               (Prims.of_int (11)))))
      (Obj.magic
         (FStar_Tactics_V2_Derived.apply_raw
            (FStar_Reflection_V2_Builtins.pack_ln
               (FStar_Reflection_V2_Data.Tv_FVar
                  (FStar_Reflection_V2_Builtins.pack_fv
                     ["FStar"; "Tactics"; "V2"; "Logic"; "__witness"])))))
      (fun uu___ ->
         (fun uu___ -> Obj.magic (FStar_Tactics_V2_Derived.exact t)) uu___)
let (elim_exists :
  FStar_Tactics_NamedView.term ->
    ((FStar_Tactics_NamedView.binding * FStar_Tactics_NamedView.binding),
      unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
               (Prims.of_int (279)) (Prims.of_int (2)) (Prims.of_int (279))
               (Prims.of_int (41)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
               (Prims.of_int (279)) (Prims.of_int (42)) (Prims.of_int (282))
               (Prims.of_int (9)))))
      (Obj.magic
         (FStar_Tactics_V2_Derived.apply_lemma
            (FStar_Reflection_V2_Builtins.pack_ln
               (FStar_Reflection_V2_Data.Tv_App
                  ((FStar_Reflection_V2_Builtins.pack_ln
                      (FStar_Reflection_V2_Data.Tv_FVar
                         (FStar_Reflection_V2_Builtins.pack_fv
                            ["FStar";
                            "Tactics";
                            "V2";
                            "Logic";
                            "__elim_exists'"]))),
                    (t, FStar_Reflection_V2_Data.Q_Explicit))))))
      (fun uu___ ->
         (fun uu___ ->
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
                          (Prims.of_int (280)) (Prims.of_int (10))
                          (Prims.of_int (280)) (Prims.of_int (18)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
                          (Prims.of_int (280)) (Prims.of_int (21))
                          (Prims.of_int (282)) (Prims.of_int (9)))))
                 (Obj.magic (FStar_Tactics_V2_Builtins.intro ()))
                 (fun uu___1 ->
                    (fun x ->
                       Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.V2.Logic.fst"
                                     (Prims.of_int (281)) (Prims.of_int (11))
                                     (Prims.of_int (281)) (Prims.of_int (19)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.V2.Logic.fst"
                                     (Prims.of_int (282)) (Prims.of_int (2))
                                     (Prims.of_int (282)) (Prims.of_int (9)))))
                            (Obj.magic (FStar_Tactics_V2_Builtins.intro ()))
                            (fun pf ->
                               FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___1 -> (x, pf))))) uu___1))) uu___)
let (instantiate :
  FStar_Tactics_NamedView.term ->
    FStar_Tactics_NamedView.term ->
      (FStar_Tactics_NamedView.binding, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun fa ->
    fun x ->
      FStar_Tactics_V2_Derived.try_with
        (fun uu___ ->
           match () with
           | () ->
               FStar_Tactics_V2_Derived.pose
                 (FStar_Reflection_V2_Builtins.pack_ln
                    (FStar_Reflection_V2_Data.Tv_App
                       ((FStar_Reflection_V2_Builtins.pack_ln
                           (FStar_Reflection_V2_Data.Tv_App
                              ((FStar_Reflection_V2_Builtins.pack_ln
                                  (FStar_Reflection_V2_Data.Tv_FVar
                                     (FStar_Reflection_V2_Builtins.pack_fv
                                        ["FStar";
                                        "Tactics";
                                        "V2";
                                        "Logic";
                                        "__forall_inst_sq"]))),
                                (fa, FStar_Reflection_V2_Data.Q_Explicit)))),
                         (x, FStar_Reflection_V2_Data.Q_Explicit)))))
        (fun uu___ ->
           FStar_Tactics_V2_Derived.try_with
             (fun uu___1 ->
                match () with
                | () ->
                    FStar_Tactics_V2_Derived.pose
                      (FStar_Reflection_V2_Builtins.pack_ln
                         (FStar_Reflection_V2_Data.Tv_App
                            ((FStar_Reflection_V2_Builtins.pack_ln
                                (FStar_Reflection_V2_Data.Tv_App
                                   ((FStar_Reflection_V2_Builtins.pack_ln
                                       (FStar_Reflection_V2_Data.Tv_FVar
                                          (FStar_Reflection_V2_Builtins.pack_fv
                                             ["FStar";
                                             "Tactics";
                                             "V2";
                                             "Logic";
                                             "__forall_inst"]))),
                                     (fa,
                                       FStar_Reflection_V2_Data.Q_Explicit)))),
                              (x, FStar_Reflection_V2_Data.Q_Explicit)))))
             (fun uu___1 ->
                (fun uu___1 ->
                   Obj.magic
                     (FStar_Tactics_V2_Derived.fail "could not instantiate"))
                  uu___1))
let (instantiate_as :
  FStar_Tactics_NamedView.term ->
    FStar_Tactics_NamedView.term ->
      Prims.string ->
        (FStar_Tactics_NamedView.binding, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun fa ->
    fun x ->
      fun s ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
                   (Prims.of_int (299)) (Prims.of_int (12))
                   (Prims.of_int (299)) (Prims.of_int (28)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
                   (Prims.of_int (300)) (Prims.of_int (4))
                   (Prims.of_int (300)) (Prims.of_int (17)))))
          (Obj.magic (instantiate fa x))
          (fun uu___ ->
             (fun b -> Obj.magic (FStar_Tactics_V2_Builtins.rename_to b s))
               uu___)
let rec (sk_binder' :
  FStar_Tactics_NamedView.binding Prims.list ->
    FStar_Tactics_NamedView.binding ->
      ((FStar_Tactics_NamedView.binding Prims.list *
         FStar_Tactics_NamedView.binding),
        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun acc ->
    fun b ->
      FStar_Tactics_V2_Derived.focus
        (fun uu___ ->
           FStar_Tactics_V2_Derived.try_with
             (fun uu___1 ->
                match () with
                | () ->
                    FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range
                               "FStar.Tactics.V2.Logic.fst"
                               (Prims.of_int (311)) (Prims.of_int (6))
                               (Prims.of_int (311)) (Prims.of_int (35)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range
                               "FStar.Tactics.V2.Logic.fst"
                               (Prims.of_int (312)) (Prims.of_int (6))
                               (Prims.of_int (316)) (Prims.of_int (29)))))
                      (Obj.magic
                         (FStar_Tactics_V2_Derived.apply_lemma
                            (FStar_Reflection_V2_Builtins.pack_ln
                               (FStar_Reflection_V2_Data.Tv_App
                                  ((FStar_Reflection_V2_Builtins.pack_ln
                                      (FStar_Reflection_V2_Data.Tv_FVar
                                         (FStar_Reflection_V2_Builtins.pack_fv
                                            ["FStar";
                                            "Tactics";
                                            "V2";
                                            "Logic";
                                            "sklem0"]))),
                                    ((FStar_Tactics_V2_SyntaxCoercions.binding_to_term
                                        b),
                                      FStar_Reflection_V2_Data.Q_Explicit))))))
                      (fun uu___2 ->
                         (fun uu___2 ->
                            Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "FStar.Tactics.V2.Logic.fst"
                                          (Prims.of_int (312))
                                          (Prims.of_int (6))
                                          (Prims.of_int (312))
                                          (Prims.of_int (38)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "FStar.Tactics.V2.Logic.fst"
                                          (Prims.of_int (313))
                                          (Prims.of_int (6))
                                          (Prims.of_int (316))
                                          (Prims.of_int (29)))))
                                 (Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.V2.Logic.fst"
                                                (Prims.of_int (312))
                                                (Prims.of_int (9))
                                                (Prims.of_int (312))
                                                (Prims.of_int (23)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.V2.Logic.fst"
                                                (Prims.of_int (312))
                                                (Prims.of_int (6))
                                                (Prims.of_int (312))
                                                (Prims.of_int (38)))))
                                       (Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "FStar.Tactics.V2.Logic.fst"
                                                      (Prims.of_int (312))
                                                      (Prims.of_int (9))
                                                      (Prims.of_int (312))
                                                      (Prims.of_int (18)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "FStar.Tactics.V2.Logic.fst"
                                                      (Prims.of_int (312))
                                                      (Prims.of_int (9))
                                                      (Prims.of_int (312))
                                                      (Prims.of_int (23)))))
                                             (Obj.magic
                                                (FStar_Tactics_V2_Derived.ngoals
                                                   ()))
                                             (fun uu___3 ->
                                                FStar_Tactics_Effect.lift_div_tac
                                                  (fun uu___4 ->
                                                     uu___3 <> Prims.int_one))))
                                       (fun uu___3 ->
                                          if uu___3
                                          then
                                            FStar_Tactics_V2_Derived.fail
                                              "no"
                                          else
                                            FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___5 -> ()))))
                                 (fun uu___3 ->
                                    (fun uu___3 ->
                                       Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "FStar.Tactics.V2.Logic.fst"
                                                     (Prims.of_int (313))
                                                     (Prims.of_int (6))
                                                     (Prims.of_int (313))
                                                     (Prims.of_int (13)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "FStar.Tactics.V2.Logic.fst"
                                                     (Prims.of_int (313))
                                                     (Prims.of_int (14))
                                                     (Prims.of_int (316))
                                                     (Prims.of_int (29)))))
                                            (Obj.magic
                                               (FStar_Tactics_V2_Builtins.clear
                                                  b))
                                            (fun uu___4 ->
                                               (fun uu___4 ->
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "FStar.Tactics.V2.Logic.fst"
                                                                (Prims.of_int (314))
                                                                (Prims.of_int (15))
                                                                (Prims.of_int (314))
                                                                (Prims.of_int (30)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "FStar.Tactics.V2.Logic.fst"
                                                                (Prims.of_int (314))
                                                                (Prims.of_int (33))
                                                                (Prims.of_int (316))
                                                                (Prims.of_int (29)))))
                                                       (Obj.magic
                                                          (forall_intro ()))
                                                       (fun uu___5 ->
                                                          (fun bx ->
                                                             Obj.magic
                                                               (FStar_Tactics_Effect.tac_bind
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Logic.fst"
                                                                    (Prims.of_int (315))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (315))
                                                                    (Prims.of_int (31)))))
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Logic.fst"
                                                                    (Prims.of_int (316))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (316))
                                                                    (Prims.of_int (29)))))
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
  FStar_Tactics_NamedView.binding ->
    ((FStar_Tactics_NamedView.binding Prims.list *
       FStar_Tactics_NamedView.binding),
      unit) FStar_Tactics_Effect.tac_repr)
  = fun b -> sk_binder' [] b
let (skolem :
  unit ->
    ((FStar_Tactics_NamedView.binding Prims.list *
       FStar_Tactics_NamedView.binding) Prims.list,
      unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
               (Prims.of_int (325)) (Prims.of_int (11)) (Prims.of_int (325))
               (Prims.of_int (35)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
               (Prims.of_int (326)) (Prims.of_int (2)) (Prims.of_int (326))
               (Prims.of_int (18)))))
      (Obj.magic
         (FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
                     (Prims.of_int (325)) (Prims.of_int (23))
                     (Prims.of_int (325)) (Prims.of_int (35)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
                     (Prims.of_int (325)) (Prims.of_int (11))
                     (Prims.of_int (325)) (Prims.of_int (35)))))
            (Obj.magic (FStar_Tactics_V2_Derived.cur_env ()))
            (fun uu___1 ->
               FStar_Tactics_Effect.lift_div_tac
                 (fun uu___2 ->
                    FStar_Reflection_V2_Builtins.vars_of_env uu___1))))
      (fun uu___1 ->
         (fun bs -> Obj.magic (FStar_Tactics_Util.map sk_binder bs)) uu___1)
let (easy_fill : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
               (Prims.of_int (335)) (Prims.of_int (12)) (Prims.of_int (335))
               (Prims.of_int (24)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
               (Prims.of_int (335)) (Prims.of_int (27)) (Prims.of_int (338))
               (Prims.of_int (10)))))
      (Obj.magic
         (FStar_Tactics_V2_Derived.repeat FStar_Tactics_V2_Builtins.intro))
      (fun uu___1 ->
         (fun uu___1 ->
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
                          (Prims.of_int (337)) (Prims.of_int (12))
                          (Prims.of_int (337)) (Prims.of_int (67)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
                          (Prims.of_int (338)) (Prims.of_int (4))
                          (Prims.of_int (338)) (Prims.of_int (10)))))
                 (Obj.magic
                    (FStar_Tactics_V2_Derived.trytac
                       (fun uu___2 ->
                          FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.V2.Logic.fst"
                                     (Prims.of_int (337)) (Prims.of_int (30))
                                     (Prims.of_int (337)) (Prims.of_int (56)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.V2.Logic.fst"
                                     (Prims.of_int (337)) (Prims.of_int (58))
                                     (Prims.of_int (337)) (Prims.of_int (66)))))
                            (Obj.magic
                               (FStar_Tactics_V2_Derived.apply
                                  (FStar_Reflection_V2_Builtins.pack_ln
                                     (FStar_Reflection_V2_Data.Tv_FVar
                                        (FStar_Reflection_V2_Builtins.pack_fv
                                           ["FStar";
                                           "Tactics";
                                           "V2";
                                           "Logic";
                                           "lemma_from_squash"])))))
                            (fun uu___3 ->
                               (fun uu___3 ->
                                  Obj.magic
                                    (FStar_Tactics_V2_Builtins.intro ()))
                                 uu___3))))
                 (fun uu___2 ->
                    (fun uu___2 ->
                       Obj.magic (FStar_Tactics_V2_Derived.smt ())) uu___2)))
           uu___1)
let easy : 'a . 'a -> 'a = fun x -> x
let (using_lemma :
  FStar_Tactics_NamedView.term ->
    (FStar_Tactics_NamedView.binding, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    FStar_Tactics_V2_Derived.try_with
      (fun uu___ ->
         match () with
         | () ->
             pose_lemma
               (FStar_Reflection_V2_Builtins.pack_ln
                  (FStar_Reflection_V2_Data.Tv_App
                     ((FStar_Reflection_V2_Builtins.pack_ln
                         (FStar_Reflection_V2_Data.Tv_FVar
                            (FStar_Reflection_V2_Builtins.pack_fv
                               ["FStar"; "Tactics"; "V2"; "Logic"; "lem1_fa"]))),
                       (t, FStar_Reflection_V2_Data.Q_Explicit)))))
      (fun uu___ ->
         FStar_Tactics_V2_Derived.try_with
           (fun uu___1 ->
              match () with
              | () ->
                  pose_lemma
                    (FStar_Reflection_V2_Builtins.pack_ln
                       (FStar_Reflection_V2_Data.Tv_App
                          ((FStar_Reflection_V2_Builtins.pack_ln
                              (FStar_Reflection_V2_Data.Tv_FVar
                                 (FStar_Reflection_V2_Builtins.pack_fv
                                    ["FStar";
                                    "Tactics";
                                    "V2";
                                    "Logic";
                                    "lem2_fa"]))),
                            (t, FStar_Reflection_V2_Data.Q_Explicit)))))
           (fun uu___1 ->
              FStar_Tactics_V2_Derived.try_with
                (fun uu___2 ->
                   match () with
                   | () ->
                       pose_lemma
                         (FStar_Reflection_V2_Builtins.pack_ln
                            (FStar_Reflection_V2_Data.Tv_App
                               ((FStar_Reflection_V2_Builtins.pack_ln
                                   (FStar_Reflection_V2_Data.Tv_FVar
                                      (FStar_Reflection_V2_Builtins.pack_fv
                                         ["FStar";
                                         "Tactics";
                                         "V2";
                                         "Logic";
                                         "lem3_fa"]))),
                                 (t, FStar_Reflection_V2_Data.Q_Explicit)))))
                (fun uu___2 ->
                   (fun uu___2 ->
                      Obj.magic
                        (FStar_Tactics_V2_Derived.fail
                           "using_lemma: failed to instantiate")) uu___2)))