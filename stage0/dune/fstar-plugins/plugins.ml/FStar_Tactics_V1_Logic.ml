open Fstarcompiler
open Prims
let cur_goal (uu___ : unit) :
  (FStarC_Reflection_Types.typ, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x =
      let x1 = FStarC_Tactics_V1_Builtins.get () ps in
      FStarC_Tactics_Types.goals_of x1 in
    match x with
    | g::uu___1 -> Obj.magic (Obj.repr (FStarC_Tactics_Types.goal_type g))
    | uu___1 ->
        Obj.magic
          (Obj.repr
             (FStarC_Tactics_V1_Builtins.raise_core
                (FStarC_Tactics_Common.TacticFailure
                   ([FStar_Pprint.arbitrary_string "no more goals"],
                     FStar_Pervasives_Native.None)) ps))
let cur_formula (uu___ : unit) :
  (FStar_Reflection_V1_Formula.formula, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = cur_goal () ps in
    FStar_Reflection_V1_Formula.term_as_formula x ps
let l_revert (uu___ : unit) : (unit, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    FStarC_Tactics_V1_Builtins.revert () ps;
    FStar_Tactics_V1_Derived.apply
      (FStarC_Reflection_V2_Builtins.pack_ln
         (FStarC_Reflection_V2_Data.Tv_FVar
            (FStarC_Reflection_V2_Builtins.pack_fv
               ["FStar"; "Tactics"; "Logic"; "Lemmas"; "revert_squash"]))) ps
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.V1.Logic.l_revert" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.V1.Logic.l_revert (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_1 l_revert)
               Fstarcompiler.FStarC_Syntax_Embeddings.e_unit
               Fstarcompiler.FStarC_Syntax_Embeddings.e_unit psc ncb us args)
let rec l_revert_all (uu___ : FStarC_Reflection_Types.binders) :
  (unit, unit) FStar_Tactics_Effect.tac_repr=
  (fun bs ->
     match bs with
     | [] -> Obj.magic (Obj.repr (fun uu___ -> ()))
     | uu___::tl ->
         Obj.magic
           (Obj.repr
              (FStar_Tactics_Effect.tac_bind (Obj.magic (l_revert ()))
                 (fun uu___1 ->
                    (fun uu___1 -> Obj.magic (l_revert_all tl)) uu___1))))
    uu___
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.V1.Logic.l_revert_all" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.V1.Logic.l_revert_all (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_1
                  l_revert_all)
               (Fstarcompiler.FStarC_Syntax_Embeddings.e_list
                  Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_binder)
               Fstarcompiler.FStarC_Syntax_Embeddings.e_unit psc ncb us args)
let forall_intro (uu___ : unit) :
  (FStarC_Reflection_Types.binder, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    FStar_Tactics_V1_Derived.apply_lemma
      (FStarC_Reflection_V2_Builtins.pack_ln
         (FStarC_Reflection_V2_Data.Tv_FVar
            (FStarC_Reflection_V2_Builtins.pack_fv
               ["FStar"; "Tactics"; "Logic"; "Lemmas"; "fa_intro_lem"]))) ps;
    FStarC_Tactics_V1_Builtins.intro () ps
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.V1.Logic.forall_intro" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.V1.Logic.forall_intro (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_1
                  forall_intro) Fstarcompiler.FStarC_Syntax_Embeddings.e_unit
               Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_binder psc ncb
               us args)
let forall_intro_as (s : Prims.string) :
  (FStarC_Reflection_Types.binder, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    FStar_Tactics_V1_Derived.apply_lemma
      (FStarC_Reflection_V2_Builtins.pack_ln
         (FStarC_Reflection_V2_Data.Tv_FVar
            (FStarC_Reflection_V2_Builtins.pack_fv
               ["FStar"; "Tactics"; "Logic"; "Lemmas"; "fa_intro_lem"]))) ps;
    FStar_Tactics_V1_Derived.intro_as s ps
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.V1.Logic.forall_intro_as" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.V1.Logic.forall_intro_as (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_1
                  forall_intro_as)
               Fstarcompiler.FStarC_Syntax_Embeddings.e_string
               Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_binder psc ncb
               us args)
let forall_intros (uu___ : unit) :
  (FStarC_Reflection_Types.binders, unit) FStar_Tactics_Effect.tac_repr=
  FStar_Tactics_V1_Derived.repeat1 forall_intro
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.V1.Logic.forall_intros" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.V1.Logic.forall_intros (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_1
                  forall_intros)
               Fstarcompiler.FStarC_Syntax_Embeddings.e_unit
               (Fstarcompiler.FStarC_Syntax_Embeddings.e_list
                  Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_binder) psc
               ncb us args)
let split (uu___ : unit) : (unit, unit) FStar_Tactics_Effect.tac_repr=
  FStar_Tactics_V1_Derived.try_with
    (fun uu___1 ->
       match () with
       | () ->
           FStar_Tactics_V1_Derived.apply_lemma
             (FStarC_Reflection_V2_Builtins.pack_ln
                (FStarC_Reflection_V2_Data.Tv_FVar
                   (FStarC_Reflection_V2_Builtins.pack_fv
                      ["FStar"; "Tactics"; "Logic"; "Lemmas"; "split_lem"]))))
    (fun uu___1 -> FStar_Tactics_V1_Derived.fail "Could not split goal")
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.V1.Logic.split" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.V1.Logic.split (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_1 split)
               Fstarcompiler.FStarC_Syntax_Embeddings.e_unit
               Fstarcompiler.FStarC_Syntax_Embeddings.e_unit psc ncb us args)
let implies_intro (uu___ : unit) :
  (FStarC_Reflection_Types.binder, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    FStar_Tactics_V1_Derived.apply_lemma
      (FStarC_Reflection_V2_Builtins.pack_ln
         (FStarC_Reflection_V2_Data.Tv_FVar
            (FStarC_Reflection_V2_Builtins.pack_fv
               ["FStar"; "Tactics"; "Logic"; "Lemmas"; "imp_intro_lem"]))) ps;
    FStarC_Tactics_V1_Builtins.intro () ps
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.V1.Logic.implies_intro" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.V1.Logic.implies_intro (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_1
                  implies_intro)
               Fstarcompiler.FStarC_Syntax_Embeddings.e_unit
               Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_binder psc ncb
               us args)
let implies_intro_as (s : Prims.string) :
  (FStarC_Reflection_Types.binder, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    FStar_Tactics_V1_Derived.apply_lemma
      (FStarC_Reflection_V2_Builtins.pack_ln
         (FStarC_Reflection_V2_Data.Tv_FVar
            (FStarC_Reflection_V2_Builtins.pack_fv
               ["FStar"; "Tactics"; "Logic"; "Lemmas"; "imp_intro_lem"]))) ps;
    FStar_Tactics_V1_Derived.intro_as s ps
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.V1.Logic.implies_intro_as" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.V1.Logic.implies_intro_as (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_1
                  implies_intro_as)
               Fstarcompiler.FStarC_Syntax_Embeddings.e_string
               Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_binder psc ncb
               us args)
let implies_intros (uu___ : unit) :
  (FStarC_Reflection_Types.binders, unit) FStar_Tactics_Effect.tac_repr=
  FStar_Tactics_V1_Derived.repeat1 implies_intro
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.V1.Logic.implies_intros" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.V1.Logic.implies_intros (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_1
                  implies_intros)
               Fstarcompiler.FStarC_Syntax_Embeddings.e_unit
               (Fstarcompiler.FStarC_Syntax_Embeddings.e_list
                  Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_binder) psc
               ncb us args)
let l_intro (uu___ : unit) :
  (FStarC_Reflection_Types.binder, unit) FStar_Tactics_Effect.tac_repr=
  FStar_Tactics_V1_Derived.or_else forall_intro implies_intro
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.V1.Logic.l_intro" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.V1.Logic.l_intro (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_1 l_intro)
               Fstarcompiler.FStarC_Syntax_Embeddings.e_unit
               Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_binder psc ncb
               us args)
let l_intros (uu___ : unit) :
  (FStarC_Reflection_Types.binder Prims.list, unit)
    FStar_Tactics_Effect.tac_repr=
  FStar_Tactics_V1_Derived.repeat l_intro
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.V1.Logic.l_intros" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.V1.Logic.l_intros (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_1 l_intros)
               Fstarcompiler.FStarC_Syntax_Embeddings.e_unit
               (Fstarcompiler.FStarC_Syntax_Embeddings.e_list
                  Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_binder) psc
               ncb us args)
let squash_intro (uu___ : unit) : (unit, unit) FStar_Tactics_Effect.tac_repr=
  FStar_Tactics_V1_Derived.apply
    (FStarC_Reflection_V2_Builtins.pack_ln
       (FStarC_Reflection_V2_Data.Tv_FVar
          (FStarC_Reflection_V2_Builtins.pack_fv
             ["FStar"; "Squash"; "return_squash"])))
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.V1.Logic.squash_intro" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.V1.Logic.squash_intro (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_1
                  squash_intro) Fstarcompiler.FStarC_Syntax_Embeddings.e_unit
               Fstarcompiler.FStarC_Syntax_Embeddings.e_unit psc ncb us args)
let l_exact (t : FStarC_Reflection_Types.term) :
  (unit, unit) FStar_Tactics_Effect.tac_repr=
  FStar_Tactics_V1_Derived.try_with
    (fun uu___ -> match () with | () -> FStar_Tactics_V1_Derived.exact t)
    (fun uu___ ps -> squash_intro () ps; FStar_Tactics_V1_Derived.exact t ps)
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.V1.Logic.l_exact" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.V1.Logic.l_exact (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_1 l_exact)
               Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term
               Fstarcompiler.FStarC_Syntax_Embeddings.e_unit psc ncb us args)
let hyp (b : FStarC_Reflection_Types.binder) :
  (unit, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = FStar_Tactics_V1_Derived.binder_to_term b ps in l_exact x ps
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.V1.Logic.hyp" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.V1.Logic.hyp (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_1 hyp)
               Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_binder
               Fstarcompiler.FStarC_Syntax_Embeddings.e_unit psc ncb us args)
let pose_lemma (t : FStarC_Reflection_Types.term) :
  (FStarC_Reflection_Types.binder, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x =
      let x1 = FStar_Tactics_V1_Derived.cur_env () ps in
      FStarC_Tactics_V1_Builtins.tcc x1 t ps in
    let x1 =
      match FStarC_Reflection_V1_Builtins.inspect_comp x with
      | FStarC_Reflection_V1_Data.C_Lemma (pre, post, uu___) -> (pre, post)
      | uu___ -> FStar_Tactics_V1_Derived.fail "" ps in
    match x1 with
    | (pre, post) ->
        let x2 =
          FStarC_Reflection_V2_Builtins.pack_ln
            (FStarC_Reflection_V2_Data.Tv_App
               (post,
                 ((FStarC_Reflection_V2_Builtins.pack_ln
                     (FStarC_Reflection_V2_Data.Tv_Const
                        FStarC_Reflection_V2_Data.C_Unit)),
                   FStarC_Reflection_V2_Data.Q_Explicit))) in
        let x3 = FStar_Tactics_V1_Derived.norm_term [] x2 ps in
        let x4 = FStar_Reflection_V1_Formula.term_as_formula' pre ps in
        (match x4 with
         | FStar_Reflection_V1_Formula.True_ ->
             FStar_Tactics_V1_Derived.pose
               (FStarC_Reflection_V2_Builtins.pack_ln
                  (FStarC_Reflection_V2_Data.Tv_App
                     ((FStarC_Reflection_V2_Builtins.pack_ln
                         (FStarC_Reflection_V2_Data.Tv_App
                            ((FStarC_Reflection_V2_Builtins.pack_ln
                                (FStarC_Reflection_V2_Data.Tv_App
                                   ((FStarC_Reflection_V2_Builtins.pack_ln
                                       (FStarC_Reflection_V2_Data.Tv_App
                                          ((FStarC_Reflection_V2_Builtins.pack_ln
                                              (FStarC_Reflection_V2_Data.Tv_FVar
                                                 (FStarC_Reflection_V2_Builtins.pack_fv
                                                    ["FStar";
                                                    "Tactics";
                                                    "Logic";
                                                    "Lemmas";
                                                    "__lemma_to_squash"]))),
                                            (pre,
                                              FStarC_Reflection_V2_Data.Q_Implicit)))),
                                     (x3,
                                       FStarC_Reflection_V2_Data.Q_Implicit)))),
                              ((FStarC_Reflection_V2_Builtins.pack_ln
                                  (FStarC_Reflection_V2_Data.Tv_Const
                                     FStarC_Reflection_V2_Data.C_Unit)),
                                FStarC_Reflection_V2_Data.Q_Explicit)))),
                       ((FStarC_Reflection_V2_Builtins.pack_ln
                           (FStarC_Reflection_V2_Data.Tv_Abs
                              ((FStarC_Reflection_V2_Builtins.pack_binder
                                  {
                                    FStarC_Reflection_V2_Data.sort2 =
                                      (FStarC_Reflection_V2_Builtins.pack_ln
                                         (FStarC_Reflection_V2_Data.Tv_FVar
                                            (FStarC_Reflection_V2_Builtins.pack_fv
                                               ["Prims"; "unit"])));
                                    FStarC_Reflection_V2_Data.qual =
                                      FStarC_Reflection_V2_Data.Q_Explicit;
                                    FStarC_Reflection_V2_Data.attrs = [];
                                    FStarC_Reflection_V2_Data.ppname2 =
                                      (FStar_Sealed.seal "uu___")
                                  }), t))),
                         FStarC_Reflection_V2_Data.Q_Explicit)))) ps
         | uu___ ->
             let x5 =
               FStar_Tactics_V1_Derived.tcut
                 (FStarC_Reflection_V2_Builtins.pack_ln
                    (FStarC_Reflection_V2_Data.Tv_App
                       ((FStarC_Reflection_V2_Builtins.pack_ln
                           (FStarC_Reflection_V2_Data.Tv_FVar
                              (FStarC_Reflection_V2_Builtins.pack_fv
                                 ["Prims"; "squash"]))),
                         (pre, FStarC_Reflection_V2_Data.Q_Explicit)))) ps in
             let x6 =
               let x7 =
                 let x8 = t in
                 let x9 = FStar_Tactics_V1_Derived.binder_to_term x5 ps in
                 FStarC_Reflection_V2_Builtins.pack_ln
                   (FStarC_Reflection_V2_Data.Tv_App
                      ((FStarC_Reflection_V2_Builtins.pack_ln
                          (FStarC_Reflection_V2_Data.Tv_App
                             ((FStarC_Reflection_V2_Builtins.pack_ln
                                 (FStarC_Reflection_V2_Data.Tv_App
                                    ((FStarC_Reflection_V2_Builtins.pack_ln
                                        (FStarC_Reflection_V2_Data.Tv_App
                                           ((FStarC_Reflection_V2_Builtins.pack_ln
                                               (FStarC_Reflection_V2_Data.Tv_FVar
                                                  (FStarC_Reflection_V2_Builtins.pack_fv
                                                     ["FStar";
                                                     "Tactics";
                                                     "Logic";
                                                     "Lemmas";
                                                     "__lemma_to_squash"]))),
                                             (pre,
                                               FStarC_Reflection_V2_Data.Q_Implicit)))),
                                      (x3,
                                        FStarC_Reflection_V2_Data.Q_Implicit)))),
                               (x9, FStarC_Reflection_V2_Data.Q_Explicit)))),
                        ((FStarC_Reflection_V2_Builtins.pack_ln
                            (FStarC_Reflection_V2_Data.Tv_Abs
                               ((FStarC_Reflection_V2_Builtins.pack_binder
                                   {
                                     FStarC_Reflection_V2_Data.sort2 =
                                       (FStarC_Reflection_V2_Builtins.pack_ln
                                          (FStarC_Reflection_V2_Data.Tv_FVar
                                             (FStarC_Reflection_V2_Builtins.pack_fv
                                                ["Prims"; "unit"])));
                                     FStarC_Reflection_V2_Data.qual =
                                       FStarC_Reflection_V2_Data.Q_Explicit;
                                     FStarC_Reflection_V2_Data.attrs = [];
                                     FStarC_Reflection_V2_Data.ppname2 =
                                       (FStar_Sealed.seal "uu___")
                                   }), x8))),
                          FStarC_Reflection_V2_Data.Q_Explicit))) in
               FStar_Tactics_V1_Derived.pose x7 ps in
             (FStar_Tactics_V1_Derived.flip () ps;
              (let x9 =
                 FStar_Tactics_V1_Derived.trytac
                   FStar_Tactics_V1_Derived.trivial ps in
               ());
              x6))
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.V1.Logic.pose_lemma" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.V1.Logic.pose_lemma (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_1 pose_lemma)
               Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term
               Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_binder psc ncb
               us args)
let explode (uu___ : unit) : (unit, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    FStar_Tactics_V1_Derived.repeatseq
      (fun uu___1 ->
         FStar_Tactics_V1_Derived.first
           [(fun uu___2 ps1 -> let x1 = l_intro () ps1 in ());
           (fun uu___2 ps1 -> split () ps1)]) ps
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.V1.Logic.explode" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.V1.Logic.explode (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_1 explode)
               Fstarcompiler.FStarC_Syntax_Embeddings.e_unit
               Fstarcompiler.FStarC_Syntax_Embeddings.e_unit psc ncb us args)
let rec visit (callback : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  : (unit, unit) FStar_Tactics_Effect.tac_repr=
  FStar_Tactics_V1_Derived.focus
    (fun uu___ ->
       FStar_Tactics_V1_Derived.or_else callback
         (fun uu___1 ps ->
            let x = FStar_Tactics_V1_Derived.cur_goal () ps in
            let x1 = FStar_Reflection_V1_Formula.term_as_formula x ps in
            match x1 with
            | FStar_Reflection_V1_Formula.Forall (_b, _sort, _phi) ->
                let x2 = forall_intros () ps in
                FStar_Tactics_V1_Derived.seq (fun uu___2 -> visit callback)
                  (fun uu___2 -> l_revert_all x2) ps
            | FStar_Reflection_V1_Formula.And (p, q) ->
                FStar_Tactics_V1_Derived.seq split
                  (fun uu___2 -> visit callback) ps
            | FStar_Reflection_V1_Formula.Implies (p, q) ->
                let x2 = implies_intro () ps in
                FStar_Tactics_V1_Derived.seq (fun uu___2 -> visit callback)
                  l_revert ps
            | uu___2 -> ()))
let rec simplify_eq_implication (uu___ : unit) :
  (unit, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = FStar_Tactics_V1_Derived.cur_env () ps in
    let x1 = FStar_Tactics_V1_Derived.cur_goal () ps in
    let x2 = FStar_Tactics_V1_Derived.destruct_equality_implication x1 ps in
    match x2 with
    | FStar_Pervasives_Native.None ->
        FStar_Tactics_V1_Derived.fail "Not an equality implication" ps
    | FStar_Pervasives_Native.Some (uu___1, rhs) ->
        let x3 = implies_intro () ps in
        (FStarC_Tactics_V1_Builtins.rewrite x3 ps;
         FStarC_Tactics_V1_Builtins.clear_top () ps;
         visit simplify_eq_implication ps)
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.V1.Logic.simplify_eq_implication" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.V1.Logic.simplify_eq_implication (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_1
                  simplify_eq_implication)
               Fstarcompiler.FStarC_Syntax_Embeddings.e_unit
               Fstarcompiler.FStarC_Syntax_Embeddings.e_unit psc ncb us args)
let rewrite_all_equalities (uu___ : unit) :
  (unit, unit) FStar_Tactics_Effect.tac_repr= visit simplify_eq_implication
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.V1.Logic.rewrite_all_equalities" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.V1.Logic.rewrite_all_equalities (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_1
                  rewrite_all_equalities)
               Fstarcompiler.FStarC_Syntax_Embeddings.e_unit
               Fstarcompiler.FStarC_Syntax_Embeddings.e_unit psc ncb us args)
let rec unfold_definition_and_simplify_eq (tm : FStarC_Reflection_Types.term)
  : (unit, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = FStar_Tactics_V1_Derived.cur_goal () ps in
    let x1 = FStar_Reflection_V1_Formula.term_as_formula x ps in
    match x1 with
    | FStar_Reflection_V1_Formula.App (hd, arg) ->
        if FStar_Reflection_TermEq_Simple.term_eq hd tm
        then FStar_Tactics_V1_Derived.trivial () ps
        else ()
    | uu___ ->
        let x2 = FStar_Tactics_V1_Derived.destruct_equality_implication x ps in
        (match x2 with
         | FStar_Pervasives_Native.None ->
             FStar_Tactics_V1_Derived.fail "Not an equality implication" ps
         | FStar_Pervasives_Native.Some (uu___1, rhs) ->
             let x3 = implies_intro () ps in
             (FStarC_Tactics_V1_Builtins.rewrite x3 ps;
              FStarC_Tactics_V1_Builtins.clear_top () ps;
              visit (fun uu___2 -> unfold_definition_and_simplify_eq tm) ps))
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.V1.Logic.unfold_definition_and_simplify_eq"
    (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.V1.Logic.unfold_definition_and_simplify_eq (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_1
                  unfold_definition_and_simplify_eq)
               Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term
               Fstarcompiler.FStarC_Syntax_Embeddings.e_unit psc ncb us args)
let unsquash (t : FStarC_Reflection_Types.term) :
  (FStarC_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x =
      FStarC_Reflection_V2_Builtins.pack_ln
        (FStarC_Reflection_V2_Data.Tv_FVar
           (FStarC_Reflection_V2_Builtins.pack_fv
              ["FStar"; "Tactics"; "Logic"; "Lemmas"; "vbind"])) in
    FStar_Tactics_V1_Derived.apply_lemma
      (FStar_Reflection_V1_Derived.mk_e_app x [t]) ps;
    (let x2 = FStarC_Tactics_V1_Builtins.intro () ps in
     FStarC_Reflection_V1_Builtins.pack_ln
       (FStarC_Reflection_V1_Data.Tv_Var
          (FStar_Reflection_V1_Derived.bv_of_binder x2)))
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.V1.Logic.unsquash" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.V1.Logic.unsquash (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_1 unsquash)
               Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term
               Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term psc ncb
               us args)
let cases_or (o : FStarC_Reflection_Types.term) :
  (unit, unit) FStar_Tactics_Effect.tac_repr=
  FStar_Tactics_V1_Derived.apply_lemma
    (FStar_Reflection_V1_Derived.mk_e_app
       (FStarC_Reflection_V2_Builtins.pack_ln
          (FStarC_Reflection_V2_Data.Tv_FVar
             (FStarC_Reflection_V2_Builtins.pack_fv
                ["FStar"; "Tactics"; "Logic"; "Lemmas"; "or_ind"]))) 
       [o])
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.V1.Logic.cases_or" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.V1.Logic.cases_or (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_1 cases_or)
               Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term
               Fstarcompiler.FStarC_Syntax_Embeddings.e_unit psc ncb us args)
let cases_bool (b : FStarC_Reflection_Types.term) :
  (unit, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x =
      FStarC_Reflection_V2_Builtins.pack_ln
        (FStarC_Reflection_V2_Data.Tv_FVar
           (FStarC_Reflection_V2_Builtins.pack_fv
              ["FStar"; "Tactics"; "Logic"; "Lemmas"; "bool_ind"])) in
    FStar_Tactics_V1_Derived.seq
      (fun uu___ ->
         FStar_Tactics_V1_Derived.apply_lemma
           (FStar_Reflection_V1_Derived.mk_e_app x [b]))
      (fun uu___ ps1 ->
         let x1 =
           FStar_Tactics_V1_Derived.trytac
             (fun uu___1 ps2 ->
                let x2 = implies_intro () ps2 in
                FStarC_Tactics_V1_Builtins.rewrite x2 ps2;
                FStarC_Tactics_V1_Builtins.clear_top () ps2) ps1 in
         ()) ps
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.V1.Logic.cases_bool" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.V1.Logic.cases_bool (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_1 cases_bool)
               Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term
               Fstarcompiler.FStarC_Syntax_Embeddings.e_unit psc ncb us args)
let left (uu___ : unit) : (unit, unit) FStar_Tactics_Effect.tac_repr=
  FStar_Tactics_V1_Derived.apply_lemma
    (FStarC_Reflection_V2_Builtins.pack_ln
       (FStarC_Reflection_V2_Data.Tv_FVar
          (FStarC_Reflection_V2_Builtins.pack_fv
             ["FStar"; "Tactics"; "Logic"; "Lemmas"; "or_intro_1"])))
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.V1.Logic.left" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.V1.Logic.left (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_1 left)
               Fstarcompiler.FStarC_Syntax_Embeddings.e_unit
               Fstarcompiler.FStarC_Syntax_Embeddings.e_unit psc ncb us args)
let right (uu___ : unit) : (unit, unit) FStar_Tactics_Effect.tac_repr=
  FStar_Tactics_V1_Derived.apply_lemma
    (FStarC_Reflection_V2_Builtins.pack_ln
       (FStarC_Reflection_V2_Data.Tv_FVar
          (FStarC_Reflection_V2_Builtins.pack_fv
             ["FStar"; "Tactics"; "Logic"; "Lemmas"; "or_intro_2"])))
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.V1.Logic.right" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.V1.Logic.right (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_1 right)
               Fstarcompiler.FStarC_Syntax_Embeddings.e_unit
               Fstarcompiler.FStarC_Syntax_Embeddings.e_unit psc ncb us args)
let and_elim (t : FStarC_Reflection_Types.term) :
  (unit, unit) FStar_Tactics_Effect.tac_repr=
  FStar_Tactics_V1_Derived.try_with
    (fun uu___ ->
       match () with
       | () ->
           FStar_Tactics_V1_Derived.apply_lemma
             (FStarC_Reflection_V2_Builtins.pack_ln
                (FStarC_Reflection_V2_Data.Tv_App
                   ((FStarC_Reflection_V2_Builtins.pack_ln
                       (FStarC_Reflection_V2_Data.Tv_FVar
                          (FStarC_Reflection_V2_Builtins.pack_fv
                             ["FStar";
                             "Tactics";
                             "Logic";
                             "Lemmas";
                             "__and_elim"]))),
                     (t, FStarC_Reflection_V2_Data.Q_Explicit)))))
    (fun uu___ ->
       FStar_Tactics_V1_Derived.apply_lemma
         (FStarC_Reflection_V2_Builtins.pack_ln
            (FStarC_Reflection_V2_Data.Tv_App
               ((FStarC_Reflection_V2_Builtins.pack_ln
                   (FStarC_Reflection_V2_Data.Tv_FVar
                      (FStarC_Reflection_V2_Builtins.pack_fv
                         ["FStar";
                         "Tactics";
                         "Logic";
                         "Lemmas";
                         "__and_elim'"]))),
                 (t, FStarC_Reflection_V2_Data.Q_Explicit)))))
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.V1.Logic.and_elim" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.V1.Logic.and_elim (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_1 and_elim)
               Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term
               Fstarcompiler.FStarC_Syntax_Embeddings.e_unit psc ncb us args)
let destruct_and (t : FStarC_Reflection_Types.term) :
  ((FStarC_Reflection_Types.binder * FStarC_Reflection_Types.binder), 
    unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    and_elim t ps;
    (let x1 = implies_intro () ps in let x2 = implies_intro () ps in (x1, x2))
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.V1.Logic.destruct_and" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.V1.Logic.destruct_and (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_1
                  destruct_and)
               Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term
               (Fstarcompiler.FStarC_Syntax_Embeddings.e_tuple2
                  Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_binder
                  Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_binder) psc
               ncb us args)
let witness (t : FStarC_Reflection_Types.term) :
  (unit, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    FStar_Tactics_V1_Derived.apply_raw
      (FStarC_Reflection_V2_Builtins.pack_ln
         (FStarC_Reflection_V2_Data.Tv_FVar
            (FStarC_Reflection_V2_Builtins.pack_fv
               ["FStar"; "Tactics"; "Logic"; "Lemmas"; "__witness"]))) ps;
    FStar_Tactics_V1_Derived.exact t ps
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.V1.Logic.witness" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.V1.Logic.witness (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_1 witness)
               Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term
               Fstarcompiler.FStarC_Syntax_Embeddings.e_unit psc ncb us args)
let elim_exists (t : FStarC_Reflection_Types.term) :
  ((FStarC_Reflection_Types.binder * FStarC_Reflection_Types.binder), 
    unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    FStar_Tactics_V1_Derived.apply_lemma
      (FStarC_Reflection_V2_Builtins.pack_ln
         (FStarC_Reflection_V2_Data.Tv_App
            ((FStarC_Reflection_V2_Builtins.pack_ln
                (FStarC_Reflection_V2_Data.Tv_FVar
                   (FStarC_Reflection_V2_Builtins.pack_fv
                      ["FStar";
                      "Tactics";
                      "Logic";
                      "Lemmas";
                      "__elim_exists'"]))),
              (t, FStarC_Reflection_V2_Data.Q_Explicit)))) ps;
    (let x1 = FStarC_Tactics_V1_Builtins.intro () ps in
     let x2 = FStarC_Tactics_V1_Builtins.intro () ps in (x1, x2))
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.V1.Logic.elim_exists" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.V1.Logic.elim_exists (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_1 elim_exists)
               Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term
               (Fstarcompiler.FStarC_Syntax_Embeddings.e_tuple2
                  Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_binder
                  Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_binder) psc
               ncb us args)
let instantiate (fa : FStarC_Reflection_Types.term)
  (x : FStarC_Reflection_Types.term) :
  (FStarC_Reflection_Types.binder, unit) FStar_Tactics_Effect.tac_repr=
  FStar_Tactics_V1_Derived.try_with
    (fun uu___ ->
       match () with
       | () ->
           FStar_Tactics_V1_Derived.pose
             (FStarC_Reflection_V2_Builtins.pack_ln
                (FStarC_Reflection_V2_Data.Tv_App
                   ((FStarC_Reflection_V2_Builtins.pack_ln
                       (FStarC_Reflection_V2_Data.Tv_App
                          ((FStarC_Reflection_V2_Builtins.pack_ln
                              (FStarC_Reflection_V2_Data.Tv_FVar
                                 (FStarC_Reflection_V2_Builtins.pack_fv
                                    ["FStar";
                                    "Tactics";
                                    "Logic";
                                    "Lemmas";
                                    "__forall_inst_sq"]))),
                            (fa, FStarC_Reflection_V2_Data.Q_Explicit)))),
                     (x, FStarC_Reflection_V2_Data.Q_Explicit)))))
    (fun uu___ ->
       FStar_Tactics_V1_Derived.try_with
         (fun uu___1 ->
            match () with
            | () ->
                FStar_Tactics_V1_Derived.pose
                  (FStarC_Reflection_V2_Builtins.pack_ln
                     (FStarC_Reflection_V2_Data.Tv_App
                        ((FStarC_Reflection_V2_Builtins.pack_ln
                            (FStarC_Reflection_V2_Data.Tv_App
                               ((FStarC_Reflection_V2_Builtins.pack_ln
                                   (FStarC_Reflection_V2_Data.Tv_FVar
                                      (FStarC_Reflection_V2_Builtins.pack_fv
                                         ["FStar";
                                         "Tactics";
                                         "Logic";
                                         "Lemmas";
                                         "__forall_inst"]))),
                                 (fa, FStarC_Reflection_V2_Data.Q_Explicit)))),
                          (x, FStarC_Reflection_V2_Data.Q_Explicit)))))
         (fun uu___1 -> FStar_Tactics_V1_Derived.fail "could not instantiate"))
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.V1.Logic.instantiate" (Prims.of_int (3))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_2
               "FStar.Tactics.V1.Logic.instantiate (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_2 instantiate)
               Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term
               Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term
               Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_binder psc ncb
               us args)
let instantiate_as (fa : FStarC_Reflection_Types.term)
  (x : FStarC_Reflection_Types.term) (s : Prims.string) :
  (FStarC_Reflection_Types.binder, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x1 = instantiate fa x ps in
    FStarC_Tactics_V1_Builtins.rename_to x1 s ps
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.V1.Logic.instantiate_as" (Prims.of_int (4))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_3
               "FStar.Tactics.V1.Logic.instantiate_as (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_3
                  instantiate_as)
               Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term
               Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term
               Fstarcompiler.FStarC_Syntax_Embeddings.e_string
               Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_binder psc ncb
               us args)
let rec sk_binder' (acc : FStarC_Reflection_Types.binders)
  (b : FStarC_Reflection_Types.binder) :
  ((FStarC_Reflection_Types.binders * FStarC_Reflection_Types.binder), 
    unit) FStar_Tactics_Effect.tac_repr=
  FStar_Tactics_V1_Derived.focus
    (fun uu___ ->
       FStar_Tactics_V1_Derived.try_with
         (fun uu___1 ->
            match () with
            | () ->
                (fun ps ->
                   (let x1 =
                      let x2 = FStar_Tactics_V1_Derived.binder_to_term b ps in
                      FStarC_Reflection_V2_Builtins.pack_ln
                        (FStarC_Reflection_V2_Data.Tv_App
                           ((FStarC_Reflection_V2_Builtins.pack_ln
                               (FStarC_Reflection_V2_Data.Tv_FVar
                                  (FStarC_Reflection_V2_Builtins.pack_fv
                                     ["FStar";
                                     "Tactics";
                                     "Logic";
                                     "Lemmas";
                                     "sklem0"]))),
                             (x2, FStarC_Reflection_V2_Data.Q_Explicit))) in
                    FStar_Tactics_V1_Derived.apply_lemma x1 ps);
                   (let x2 =
                      let x3 = FStar_Tactics_V1_Derived.ngoals () ps in
                      x3 <> Prims.int_one in
                    if x2 then FStar_Tactics_V1_Derived.fail "no" ps else ());
                   FStarC_Tactics_V1_Builtins.clear b ps;
                   (let x3 = forall_intro () ps in
                    let x4 = implies_intro () ps in
                    sk_binder' (x3 :: acc) x4 ps)))
         (fun uu___1 ->
            (fun uu___1 -> Obj.magic (fun uu___2 -> (acc, b))) uu___1))
let sk_binder (b : FStarC_Reflection_Types.binder) :
  ((FStarC_Reflection_Types.binders * FStarC_Reflection_Types.binder), 
    unit) FStar_Tactics_Effect.tac_repr=
  sk_binder' [] b
let skolem (uu___ : unit) :
  ((FStarC_Reflection_Types.binders * FStarC_Reflection_Types.binder)
     Prims.list,
    unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x =
      let x1 = FStar_Tactics_V1_Derived.cur_env () ps in
      FStarC_Reflection_V1_Builtins.binders_of_env x1 in
    FStar_Tactics_Util.map sk_binder x ps
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.V1.Logic.skolem" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.V1.Logic.skolem (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_1 skolem)
               Fstarcompiler.FStarC_Syntax_Embeddings.e_unit
               (Fstarcompiler.FStarC_Syntax_Embeddings.e_list
                  (Fstarcompiler.FStarC_Syntax_Embeddings.e_tuple2
                     (Fstarcompiler.FStarC_Syntax_Embeddings.e_list
                        Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_binder)
                     Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_binder))
               psc ncb us args)
let easy_fill (uu___ : unit) : (unit, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x =
      FStar_Tactics_V1_Derived.repeat FStarC_Tactics_V1_Builtins.intro ps in
    let x1 =
      FStar_Tactics_V1_Derived.trytac
        (fun uu___1 ps1 ->
           FStar_Tactics_V1_Derived.apply
             (FStarC_Reflection_V2_Builtins.pack_ln
                (FStarC_Reflection_V2_Data.Tv_FVar
                   (FStarC_Reflection_V2_Builtins.pack_fv
                      ["FStar";
                      "Tactics";
                      "Logic";
                      "Lemmas";
                      "lemma_from_squash"]))) ps1;
           FStarC_Tactics_V1_Builtins.intro () ps1) ps in
    FStar_Tactics_V1_Derived.smt () ps
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.V1.Logic.easy_fill" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.V1.Logic.easy_fill (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_1 easy_fill)
               Fstarcompiler.FStarC_Syntax_Embeddings.e_unit
               Fstarcompiler.FStarC_Syntax_Embeddings.e_unit psc ncb us args)
let easy (x : 'a) : 'a= x
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_plugin
    "FStar.Tactics.V1.Logic.easy" (Prims.of_int (2))
    (fun _psc ->
       fun cb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Syntax_Embeddings.debug_wrap
               "FStar.Tactics.V1.Logic.easy"
               (fun _ ->
                  match args with
                  | (tv_0, _)::args_tail ->
                      (Fstarcompiler.FStarC_Syntax_Embeddings.arrow_as_prim_step_1
                         (Fstarcompiler.FStarC_Syntax_Embeddings.mk_any_emb
                            tv_0)
                         (Fstarcompiler.FStarC_Syntax_Embeddings.mk_any_emb
                            tv_0) easy
                         (Fstarcompiler.FStarC_Ident.lid_of_str
                            "FStar.Tactics.V1.Logic.easy") cb us) args_tail
                  | _ -> failwith "arity mismatch"))
    (fun cb ->
       fun us ->
         fun args ->
           Fstarcompiler.FStarC_Syntax_Embeddings.debug_wrap
             "FStar.Tactics.V1.Logic.easy"
             (fun _ ->
                match args with
                | (tv_0, _)::args_tail ->
                    (Fstarcompiler.FStarC_TypeChecker_NBETerm.arrow_as_prim_step_1
                       (Fstarcompiler.FStarC_TypeChecker_NBETerm.mk_any_emb
                          tv_0)
                       (Fstarcompiler.FStarC_TypeChecker_NBETerm.mk_any_emb
                          tv_0) easy
                       (Fstarcompiler.FStarC_Ident.lid_of_str
                          "FStar.Tactics.V1.Logic.easy") cb us) args_tail
                | _ -> failwith "arity mismatch"))
let using_lemma (t : FStarC_Reflection_Types.term) :
  (FStarC_Reflection_Types.binder, unit) FStar_Tactics_Effect.tac_repr=
  FStar_Tactics_V1_Derived.try_with
    (fun uu___ ->
       match () with
       | () ->
           pose_lemma
             (FStarC_Reflection_V2_Builtins.pack_ln
                (FStarC_Reflection_V2_Data.Tv_App
                   ((FStarC_Reflection_V2_Builtins.pack_ln
                       (FStarC_Reflection_V2_Data.Tv_FVar
                          (FStarC_Reflection_V2_Builtins.pack_fv
                             ["FStar";
                             "Tactics";
                             "Logic";
                             "Lemmas";
                             "lem1_fa"]))),
                     (t, FStarC_Reflection_V2_Data.Q_Explicit)))))
    (fun uu___ ->
       FStar_Tactics_V1_Derived.try_with
         (fun uu___1 ->
            match () with
            | () ->
                pose_lemma
                  (FStarC_Reflection_V2_Builtins.pack_ln
                     (FStarC_Reflection_V2_Data.Tv_App
                        ((FStarC_Reflection_V2_Builtins.pack_ln
                            (FStarC_Reflection_V2_Data.Tv_FVar
                               (FStarC_Reflection_V2_Builtins.pack_fv
                                  ["FStar";
                                  "Tactics";
                                  "Logic";
                                  "Lemmas";
                                  "lem2_fa"]))),
                          (t, FStarC_Reflection_V2_Data.Q_Explicit)))))
         (fun uu___1 ->
            FStar_Tactics_V1_Derived.try_with
              (fun uu___2 ->
                 match () with
                 | () ->
                     pose_lemma
                       (FStarC_Reflection_V2_Builtins.pack_ln
                          (FStarC_Reflection_V2_Data.Tv_App
                             ((FStarC_Reflection_V2_Builtins.pack_ln
                                 (FStarC_Reflection_V2_Data.Tv_FVar
                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                       ["FStar";
                                       "Tactics";
                                       "Logic";
                                       "Lemmas";
                                       "lem3_fa"]))),
                               (t, FStarC_Reflection_V2_Data.Q_Explicit)))))
              (fun uu___2 ->
                 FStar_Tactics_V1_Derived.fail
                   "using_lemma: failed to instantiate")))
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.V1.Logic.using_lemma" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.V1.Logic.using_lemma (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_1 using_lemma)
               Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_term
               Fstarcompiler.FStarC_Reflection_V2_Embeddings.e_binder psc ncb
               us args)
