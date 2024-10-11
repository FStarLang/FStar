open Prims
let (cur_goal :
  unit -> (FStarC_Reflection_Types.typ, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    let uu___1 =
      let uu___2 = Obj.magic (FStar_Tactics_Effect.get ()) in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fsti"
                 (Prims.of_int (28)) (Prims.of_int (17)) (Prims.of_int (28))
                 (Prims.of_int (25)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fsti"
                 (Prims.of_int (28)) (Prims.of_int (8)) (Prims.of_int (28))
                 (Prims.of_int (25))))) (Obj.magic uu___2)
        (fun uu___3 ->
           FStar_Tactics_Effect.lift_div_tac
             (fun uu___4 -> FStarC_Tactics_Types.goals_of uu___3)) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fsti"
               (Prims.of_int (28)) (Prims.of_int (8)) (Prims.of_int (28))
               (Prims.of_int (25)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fsti"
               (Prims.of_int (28)) (Prims.of_int (2)) (Prims.of_int (30))
               (Prims.of_int (60))))) (Obj.magic uu___1)
      (fun uu___2 ->
         match uu___2 with
         | g::uu___3 ->
             FStar_Tactics_Effect.lift_div_tac
               (fun uu___4 -> FStarC_Tactics_Types.goal_type g)
         | uu___3 ->
             FStar_Tactics_Effect.raise
               (FStarC_Tactics_Common.TacticFailure
                  ([FStarC_Pprint.arbitrary_string "no more goals"],
                    FStar_Pervasives_Native.None)))
let (cur_formula :
  unit ->
    (FStar_Reflection_V2_Formula.formula, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    let uu___1 = cur_goal () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fsti"
               (Prims.of_int (33)) (Prims.of_int (51)) (Prims.of_int (33))
               (Prims.of_int (64)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fsti"
               (Prims.of_int (33)) (Prims.of_int (35)) (Prims.of_int (33))
               (Prims.of_int (64))))) (Obj.magic uu___1)
      (fun uu___2 ->
         (fun uu___2 ->
            Obj.magic (FStar_Reflection_V2_Formula.term_as_formula uu___2))
           uu___2)
let (term_eq :
  FStarC_Reflection_Types.term -> FStarC_Reflection_Types.term -> Prims.bool)
  = FStar_Reflection_TermEq_Simple.term_eq
let (l_revert : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    let uu___1 = FStarC_Tactics_V2_Builtins.revert () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
               (Prims.of_int (34)) (Prims.of_int (4)) (Prims.of_int (34))
               (Prims.of_int (13)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
               (Prims.of_int (35)) (Prims.of_int (4)) (Prims.of_int (35))
               (Prims.of_int (26))))) (Obj.magic uu___1)
      (fun uu___2 ->
         (fun uu___2 ->
            Obj.magic
              (FStar_Tactics_V2_Derived.apply
                 (FStarC_Reflection_V2_Builtins.pack_ln
                    (FStarC_Reflection_V2_Data.Tv_FVar
                       (FStarC_Reflection_V2_Builtins.pack_fv
                          ["FStar";
                          "Tactics";
                          "V1";
                          "Logic";
                          "Lemmas";
                          "revert_squash"]))))) uu___2)
let _ =
  FStarC_Tactics_Native.register_tactic "FStar.Tactics.V2.Logic.l_revert"
    (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.V2.Logic.l_revert (plugin)"
               (FStarC_Tactics_Native.from_tactic_1 l_revert)
               FStarC_Syntax_Embeddings.e_unit
               FStarC_Syntax_Embeddings.e_unit psc ncb us args)
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
                (let uu___1 = l_revert () in
                 FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
                            (Prims.of_int (41)) (Prims.of_int (21))
                            (Prims.of_int (41)) (Prims.of_int (32)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
                            (Prims.of_int (41)) (Prims.of_int (34))
                            (Prims.of_int (41)) (Prims.of_int (49)))))
                   (Obj.magic uu___1)
                   (fun uu___2 ->
                      (fun uu___2 -> Obj.magic (l_revert_all tl)) uu___2))))
      uu___
let _ =
  FStarC_Tactics_Native.register_tactic "FStar.Tactics.V2.Logic.l_revert_all"
    (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.V2.Logic.l_revert_all (plugin)"
               (FStarC_Tactics_Native.from_tactic_1 l_revert_all)
               (FStarC_Syntax_Embeddings.e_list
                  FStarC_Reflection_V2_Embeddings.e_binding)
               FStarC_Syntax_Embeddings.e_unit psc ncb us args)
let (forall_intro :
  unit ->
    (FStar_Tactics_NamedView.binding, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    let uu___1 =
      FStar_Tactics_V2_Derived.apply_lemma
        (FStarC_Reflection_V2_Builtins.pack_ln
           (FStarC_Reflection_V2_Data.Tv_FVar
              (FStarC_Reflection_V2_Builtins.pack_fv
                 ["FStar";
                 "Tactics";
                 "V1";
                 "Logic";
                 "Lemmas";
                 "fa_intro_lem"]))) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
               (Prims.of_int (45)) (Prims.of_int (4)) (Prims.of_int (45))
               (Prims.of_int (31)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
               (Prims.of_int (46)) (Prims.of_int (4)) (Prims.of_int (46))
               (Prims.of_int (12))))) (Obj.magic uu___1)
      (fun uu___2 ->
         (fun uu___2 -> Obj.magic (FStarC_Tactics_V2_Builtins.intro ()))
           uu___2)
let _ =
  FStarC_Tactics_Native.register_tactic "FStar.Tactics.V2.Logic.forall_intro"
    (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.V2.Logic.forall_intro (plugin)"
               (FStarC_Tactics_Native.from_tactic_1 forall_intro)
               FStarC_Syntax_Embeddings.e_unit
               FStarC_Reflection_V2_Embeddings.e_binding psc ncb us args)
let (forall_intro_as :
  Prims.string ->
    (FStar_Tactics_NamedView.binding, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun s ->
    let uu___ =
      FStar_Tactics_V2_Derived.apply_lemma
        (FStarC_Reflection_V2_Builtins.pack_ln
           (FStarC_Reflection_V2_Data.Tv_FVar
              (FStarC_Reflection_V2_Builtins.pack_fv
                 ["FStar";
                 "Tactics";
                 "V1";
                 "Logic";
                 "Lemmas";
                 "fa_intro_lem"]))) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
               (Prims.of_int (50)) (Prims.of_int (4)) (Prims.of_int (50))
               (Prims.of_int (31)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
               (Prims.of_int (51)) (Prims.of_int (4)) (Prims.of_int (51))
               (Prims.of_int (14))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun uu___1 -> Obj.magic (FStar_Tactics_V2_Derived.intro_as s))
           uu___1)
let _ =
  FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.V2.Logic.forall_intro_as" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.V2.Logic.forall_intro_as (plugin)"
               (FStarC_Tactics_Native.from_tactic_1 forall_intro_as)
               FStarC_Syntax_Embeddings.e_string
               FStarC_Reflection_V2_Embeddings.e_binding psc ncb us args)
let (forall_intros :
  unit ->
    (FStar_Tactics_NamedView.binding Prims.list, unit)
      FStar_Tactics_Effect.tac_repr)
  = fun uu___ -> FStar_Tactics_V2_Derived.repeat1 forall_intro
let _ =
  FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.V2.Logic.forall_intros" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.V2.Logic.forall_intros (plugin)"
               (FStarC_Tactics_Native.from_tactic_1 forall_intros)
               FStarC_Syntax_Embeddings.e_unit
               (FStarC_Syntax_Embeddings.e_list
                  FStarC_Reflection_V2_Embeddings.e_binding) psc ncb us args)
let (split : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_V2_Derived.try_with
      (fun uu___1 ->
         match () with
         | () ->
             FStar_Tactics_V2_Derived.apply_lemma
               (FStarC_Reflection_V2_Builtins.pack_ln
                  (FStarC_Reflection_V2_Data.Tv_FVar
                     (FStarC_Reflection_V2_Builtins.pack_fv
                        ["FStar";
                        "Tactics";
                        "V1";
                        "Logic";
                        "Lemmas";
                        "split_lem"]))))
      (fun uu___1 ->
         (fun uu___1 ->
            Obj.magic (FStar_Tactics_V2_Derived.fail "Could not split goal"))
           uu___1)
let _ =
  FStarC_Tactics_Native.register_tactic "FStar.Tactics.V2.Logic.split"
    (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.V2.Logic.split (plugin)"
               (FStarC_Tactics_Native.from_tactic_1 split)
               FStarC_Syntax_Embeddings.e_unit
               FStarC_Syntax_Embeddings.e_unit psc ncb us args)
let (implies_intro :
  unit ->
    (FStar_Tactics_NamedView.binding, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    let uu___1 =
      FStar_Tactics_V2_Derived.apply_lemma
        (FStarC_Reflection_V2_Builtins.pack_ln
           (FStarC_Reflection_V2_Data.Tv_FVar
              (FStarC_Reflection_V2_Builtins.pack_fv
                 ["FStar";
                 "Tactics";
                 "V1";
                 "Logic";
                 "Lemmas";
                 "imp_intro_lem"]))) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
               (Prims.of_int (63)) (Prims.of_int (4)) (Prims.of_int (63))
               (Prims.of_int (32)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
               (Prims.of_int (64)) (Prims.of_int (4)) (Prims.of_int (64))
               (Prims.of_int (12))))) (Obj.magic uu___1)
      (fun uu___2 ->
         (fun uu___2 -> Obj.magic (FStarC_Tactics_V2_Builtins.intro ()))
           uu___2)
let _ =
  FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.V2.Logic.implies_intro" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.V2.Logic.implies_intro (plugin)"
               (FStarC_Tactics_Native.from_tactic_1 implies_intro)
               FStarC_Syntax_Embeddings.e_unit
               FStarC_Reflection_V2_Embeddings.e_binding psc ncb us args)
let (implies_intro_as :
  Prims.string ->
    (FStar_Tactics_NamedView.binding, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun s ->
    let uu___ =
      FStar_Tactics_V2_Derived.apply_lemma
        (FStarC_Reflection_V2_Builtins.pack_ln
           (FStarC_Reflection_V2_Data.Tv_FVar
              (FStarC_Reflection_V2_Builtins.pack_fv
                 ["FStar";
                 "Tactics";
                 "V1";
                 "Logic";
                 "Lemmas";
                 "imp_intro_lem"]))) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
               (Prims.of_int (67)) (Prims.of_int (4)) (Prims.of_int (67))
               (Prims.of_int (32)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
               (Prims.of_int (68)) (Prims.of_int (4)) (Prims.of_int (68))
               (Prims.of_int (14))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun uu___1 -> Obj.magic (FStar_Tactics_V2_Derived.intro_as s))
           uu___1)
let _ =
  FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.V2.Logic.implies_intro_as" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.V2.Logic.implies_intro_as (plugin)"
               (FStarC_Tactics_Native.from_tactic_1 implies_intro_as)
               FStarC_Syntax_Embeddings.e_string
               FStarC_Reflection_V2_Embeddings.e_binding psc ncb us args)
let (implies_intros :
  unit ->
    (FStar_Tactics_NamedView.binding Prims.list, unit)
      FStar_Tactics_Effect.tac_repr)
  = fun uu___ -> FStar_Tactics_V2_Derived.repeat1 implies_intro
let _ =
  FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.V2.Logic.implies_intros" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.V2.Logic.implies_intros (plugin)"
               (FStarC_Tactics_Native.from_tactic_1 implies_intros)
               FStarC_Syntax_Embeddings.e_unit
               (FStarC_Syntax_Embeddings.e_list
                  FStarC_Reflection_V2_Embeddings.e_binding) psc ncb us args)
let (l_intro :
  unit ->
    (FStar_Tactics_NamedView.binding, unit) FStar_Tactics_Effect.tac_repr)
  = fun uu___ -> FStar_Tactics_V2_Derived.or_else forall_intro implies_intro
let _ =
  FStarC_Tactics_Native.register_tactic "FStar.Tactics.V2.Logic.l_intro"
    (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.V2.Logic.l_intro (plugin)"
               (FStarC_Tactics_Native.from_tactic_1 l_intro)
               FStarC_Syntax_Embeddings.e_unit
               FStarC_Reflection_V2_Embeddings.e_binding psc ncb us args)
let (l_intros :
  unit ->
    (FStar_Tactics_NamedView.binding Prims.list, unit)
      FStar_Tactics_Effect.tac_repr)
  = fun uu___ -> FStar_Tactics_V2_Derived.repeat l_intro
let _ =
  FStarC_Tactics_Native.register_tactic "FStar.Tactics.V2.Logic.l_intros"
    (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.V2.Logic.l_intros (plugin)"
               (FStarC_Tactics_Native.from_tactic_1 l_intros)
               FStarC_Syntax_Embeddings.e_unit
               (FStarC_Syntax_Embeddings.e_list
                  FStarC_Reflection_V2_Embeddings.e_binding) psc ncb us args)
let (squash_intro : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_V2_Derived.apply
      (FStarC_Reflection_V2_Builtins.pack_ln
         (FStarC_Reflection_V2_Data.Tv_FVar
            (FStarC_Reflection_V2_Builtins.pack_fv
               ["FStar"; "Squash"; "return_squash"])))
let _ =
  FStarC_Tactics_Native.register_tactic "FStar.Tactics.V2.Logic.squash_intro"
    (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.V2.Logic.squash_intro (plugin)"
               (FStarC_Tactics_Native.from_tactic_1 squash_intro)
               FStarC_Syntax_Embeddings.e_unit
               FStarC_Syntax_Embeddings.e_unit psc ncb us args)
let (l_exact :
  FStar_Tactics_NamedView.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    FStar_Tactics_V2_Derived.try_with
      (fun uu___ -> match () with | () -> FStar_Tactics_V2_Derived.exact t)
      (fun uu___ ->
         let uu___1 = squash_intro () in
         FStar_Tactics_Effect.tac_bind
           (FStar_Sealed.seal
              (Obj.magic
                 (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
                    (Prims.of_int (84)) (Prims.of_int (12))
                    (Prims.of_int (84)) (Prims.of_int (27)))))
           (FStar_Sealed.seal
              (Obj.magic
                 (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
                    (Prims.of_int (84)) (Prims.of_int (29))
                    (Prims.of_int (84)) (Prims.of_int (36)))))
           (Obj.magic uu___1)
           (fun uu___2 ->
              (fun uu___2 -> Obj.magic (FStar_Tactics_V2_Derived.exact t))
                uu___2))
let _ =
  FStarC_Tactics_Native.register_tactic "FStar.Tactics.V2.Logic.l_exact"
    (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.V2.Logic.l_exact (plugin)"
               (FStarC_Tactics_Native.from_tactic_1 l_exact)
               FStarC_Reflection_V2_Embeddings.e_term
               FStarC_Syntax_Embeddings.e_unit psc ncb us args)
let (hyp :
  FStar_Tactics_NamedView.namedv ->
    (unit, unit) FStar_Tactics_Effect.tac_repr)
  = fun x -> l_exact (FStar_Tactics_V2_SyntaxCoercions.namedv_to_term x)
let _ =
  FStarC_Tactics_Native.register_tactic "FStar.Tactics.V2.Logic.hyp"
    (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.V2.Logic.hyp (plugin)"
               (FStarC_Tactics_Native.from_tactic_1 hyp)
               FStarC_Reflection_V2_Embeddings.e_namedv_view
               FStarC_Syntax_Embeddings.e_unit psc ncb us args)
let (pose_lemma :
  FStar_Tactics_NamedView.term ->
    (FStar_Tactics_NamedView.binding, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    let uu___ =
      let uu___1 = FStar_Tactics_V2_Derived.cur_env () in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
                 (Prims.of_int (91)) (Prims.of_int (14)) (Prims.of_int (91))
                 (Prims.of_int (26)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
                 (Prims.of_int (91)) (Prims.of_int (10)) (Prims.of_int (91))
                 (Prims.of_int (28))))) (Obj.magic uu___1)
        (fun uu___2 ->
           (fun uu___2 -> Obj.magic (FStar_Tactics_NamedView.tcc uu___2 t))
             uu___2) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
               (Prims.of_int (91)) (Prims.of_int (10)) (Prims.of_int (91))
               (Prims.of_int (28)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
               (Prims.of_int (91)) (Prims.of_int (31)) (Prims.of_int (109))
               (Prims.of_int (5))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun c ->
            let uu___1 =
              match c with
              | FStarC_Reflection_V2_Data.C_Lemma (pre, post, uu___2) ->
                  Obj.magic
                    (FStar_Tactics_Effect.lift_div_tac
                       (fun uu___3 -> (pre, post)))
              | uu___2 -> Obj.magic (FStar_Tactics_V2_Derived.fail "") in
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
                          (Prims.of_int (93)) (Prims.of_int (4))
                          (Prims.of_int (95)) (Prims.of_int (18)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
                          (Prims.of_int (91)) (Prims.of_int (31))
                          (Prims.of_int (109)) (Prims.of_int (5)))))
                 (Obj.magic uu___1)
                 (fun uu___2 ->
                    (fun uu___2 ->
                       match uu___2 with
                       | (pre, post) ->
                           let uu___3 =
                             Obj.magic
                               (FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___4 ->
                                     FStarC_Reflection_V2_Builtins.pack_ln
                                       (FStarC_Reflection_V2_Data.Tv_App
                                          (post,
                                            ((FStarC_Reflection_V2_Builtins.pack_ln
                                                (FStarC_Reflection_V2_Data.Tv_Const
                                                   FStarC_Reflection_V2_Data.C_Unit)),
                                              FStarC_Reflection_V2_Data.Q_Explicit))))) in
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.V2.Logic.fst"
                                         (Prims.of_int (97))
                                         (Prims.of_int (13))
                                         (Prims.of_int (97))
                                         (Prims.of_int (27)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.V2.Logic.fst"
                                         (Prims.of_int (97))
                                         (Prims.of_int (30))
                                         (Prims.of_int (109))
                                         (Prims.of_int (5)))))
                                (Obj.magic uu___3)
                                (fun uu___4 ->
                                   (fun post1 ->
                                      let uu___4 =
                                        FStar_Tactics_V2_Derived.norm_term []
                                          post1 in
                                      Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "FStar.Tactics.V2.Logic.fst"
                                                    (Prims.of_int (98))
                                                    (Prims.of_int (13))
                                                    (Prims.of_int (98))
                                                    (Prims.of_int (30)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "FStar.Tactics.V2.Logic.fst"
                                                    (Prims.of_int (100))
                                                    (Prims.of_int (2))
                                                    (Prims.of_int (109))
                                                    (Prims.of_int (5)))))
                                           (Obj.magic uu___4)
                                           (fun uu___5 ->
                                              (fun post2 ->
                                                 let uu___5 =
                                                   FStar_Reflection_V2_Formula.term_as_formula'
                                                     pre in
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "FStar.Tactics.V2.Logic.fst"
                                                               (Prims.of_int (100))
                                                               (Prims.of_int (8))
                                                               (Prims.of_int (100))
                                                               (Prims.of_int (28)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "FStar.Tactics.V2.Logic.fst"
                                                               (Prims.of_int (100))
                                                               (Prims.of_int (2))
                                                               (Prims.of_int (109))
                                                               (Prims.of_int (5)))))
                                                      (Obj.magic uu___5)
                                                      (fun uu___6 ->
                                                         (fun uu___6 ->
                                                            match uu___6 with
                                                            | FStar_Reflection_V2_Formula.True_
                                                                ->
                                                                Obj.magic
                                                                  (FStar_Tactics_V2_Derived.pose
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
                                                                    "V1";
                                                                    "Logic";
                                                                    "Lemmas";
                                                                    "__lemma_to_squash"]))),
                                                                    (pre,
                                                                    FStarC_Reflection_V2_Data.Q_Implicit)))),
                                                                    (post2,
                                                                    FStarC_Reflection_V2_Data.Q_Implicit)))),
                                                                    ((FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_Const
                                                                    FStarC_Reflection_V2_Data.C_Unit)),
                                                                    FStarC_Reflection_V2_Data.Q_Explicit)))),
                                                                    ((FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_Abs
                                                                    ((FStarC_Reflection_V2_Builtins.pack_binder
                                                                    {
                                                                    FStarC_Reflection_V2_Data.sort2
                                                                    =
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["Prims";
                                                                    "unit"])));
                                                                    FStarC_Reflection_V2_Data.qual
                                                                    =
                                                                    FStarC_Reflection_V2_Data.Q_Explicit;
                                                                    FStarC_Reflection_V2_Data.attrs
                                                                    = [];
                                                                    FStarC_Reflection_V2_Data.ppname2
                                                                    =
                                                                    (FStar_Sealed.seal
                                                                    "uu___")
                                                                    }), t))),
                                                                    FStarC_Reflection_V2_Data.Q_Explicit)))))
                                                            | uu___7 ->
                                                                let uu___8 =
                                                                  FStar_Tactics_V2_Derived.tcut
                                                                    (
                                                                    FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_App
                                                                    ((FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["Prims";
                                                                    "squash"]))),
                                                                    (pre,
                                                                    FStarC_Reflection_V2_Data.Q_Explicit)))) in
                                                                Obj.magic
                                                                  (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Logic.fst"
                                                                    (Prims.of_int (104))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (104))
                                                                    (Prims.of_int (37)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Logic.fst"
                                                                    (Prims.of_int (104))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (109))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun reqb
                                                                    ->
                                                                    let uu___9
                                                                    =
                                                                    FStar_Tactics_V2_Derived.pose
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
                                                                    "V1";
                                                                    "Logic";
                                                                    "Lemmas";
                                                                    "__lemma_to_squash"]))),
                                                                    (pre,
                                                                    FStarC_Reflection_V2_Data.Q_Implicit)))),
                                                                    (post2,
                                                                    FStarC_Reflection_V2_Data.Q_Implicit)))),
                                                                    ((FStar_Tactics_V2_SyntaxCoercions.binding_to_term
                                                                    reqb),
                                                                    FStarC_Reflection_V2_Data.Q_Explicit)))),
                                                                    ((FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_Abs
                                                                    ((FStarC_Reflection_V2_Builtins.pack_binder
                                                                    {
                                                                    FStarC_Reflection_V2_Data.sort2
                                                                    =
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["Prims";
                                                                    "unit"])));
                                                                    FStarC_Reflection_V2_Data.qual
                                                                    =
                                                                    FStarC_Reflection_V2_Data.Q_Explicit;
                                                                    FStarC_Reflection_V2_Data.attrs
                                                                    = [];
                                                                    FStarC_Reflection_V2_Data.ppname2
                                                                    =
                                                                    (FStar_Sealed.seal
                                                                    "uu___")
                                                                    }), t))),
                                                                    FStarC_Reflection_V2_Data.Q_Explicit)))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Logic.fst"
                                                                    (Prims.of_int (106))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (106))
                                                                    (Prims.of_int (95)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Logic.fst"
                                                                    (Prims.of_int (107))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (109))
                                                                    (Prims.of_int (5)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun b ->
                                                                    let uu___10
                                                                    =
                                                                    FStar_Tactics_V2_Derived.flip
                                                                    () in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Logic.fst"
                                                                    (Prims.of_int (107))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (107))
                                                                    (Prims.of_int (11)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Logic.fst"
                                                                    (Prims.of_int (108))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (109))
                                                                    (Prims.of_int (5)))))
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
                                                                    FStar_Tactics_V2_Derived.trytac
                                                                    FStar_Tactics_V2_Derived.trivial in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Logic.fst"
                                                                    (Prims.of_int (108))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (108))
                                                                    (Prims.of_int (27)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Logic.fst"
                                                                    (Prims.of_int (108))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (108))
                                                                    (Prims.of_int (27)))))
                                                                    (Obj.magic
                                                                    uu___13)
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___15
                                                                    -> ())) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Logic.fst"
                                                                    (Prims.of_int (108))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (108))
                                                                    (Prims.of_int (27)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Logic.fst"
                                                                    (Prims.of_int (106))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (106))
                                                                    (Prims.of_int (9)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___14
                                                                    -> b))))
                                                                    uu___11)))
                                                                    uu___10)))
                                                                    uu___9)))
                                                           uu___6))) uu___5)))
                                     uu___4))) uu___2))) uu___1)
let _ =
  FStarC_Tactics_Native.register_tactic "FStar.Tactics.V2.Logic.pose_lemma"
    (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.V2.Logic.pose_lemma (plugin)"
               (FStarC_Tactics_Native.from_tactic_1 pose_lemma)
               FStarC_Reflection_V2_Embeddings.e_term
               FStarC_Reflection_V2_Embeddings.e_binding psc ncb us args)
let (explode : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    let uu___1 =
      FStar_Tactics_V2_Derived.repeatseq
        (fun uu___2 ->
           FStar_Tactics_V2_Derived.first
             [(fun uu___3 ->
                 let uu___4 = l_intro () in
                 FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
                            (Prims.of_int (113)) (Prims.of_int (50))
                            (Prims.of_int (113)) (Prims.of_int (62)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
                            (Prims.of_int (113)) (Prims.of_int (43))
                            (Prims.of_int (113)) (Prims.of_int (62)))))
                   (Obj.magic uu___4)
                   (fun uu___5 ->
                      FStar_Tactics_Effect.lift_div_tac (fun uu___6 -> ())));
             (fun uu___3 ->
                let uu___4 = split () in
                FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
                           (Prims.of_int (114)) (Prims.of_int (50))
                           (Prims.of_int (114)) (Prims.of_int (60)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
                           (Prims.of_int (114)) (Prims.of_int (43))
                           (Prims.of_int (114)) (Prims.of_int (60)))))
                  (Obj.magic uu___4)
                  (fun uu___5 ->
                     FStar_Tactics_Effect.lift_div_tac (fun uu___6 -> ())))]) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
               (Prims.of_int (112)) (Prims.of_int (11)) (Prims.of_int (114))
               (Prims.of_int (64)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
               (Prims.of_int (112)) (Prims.of_int (4)) (Prims.of_int (114))
               (Prims.of_int (64))))) (Obj.magic uu___1)
      (fun uu___2 -> FStar_Tactics_Effect.lift_div_tac (fun uu___3 -> ()))
let _ =
  FStarC_Tactics_Native.register_tactic "FStar.Tactics.V2.Logic.explode"
    (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.V2.Logic.explode (plugin)"
               (FStarC_Tactics_Native.from_tactic_1 explode)
               FStarC_Syntax_Embeddings.e_unit
               FStarC_Syntax_Embeddings.e_unit psc ncb us args)
let rec (visit :
  (unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) ->
    (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun callback ->
    FStar_Tactics_V2_Derived.focus
      (fun uu___ ->
         FStar_Tactics_V2_Derived.or_else callback
           (fun uu___1 ->
              let uu___2 = FStar_Tactics_V2_Derived.cur_goal () in
              FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
                         (Prims.of_int (120)) (Prims.of_int (28))
                         (Prims.of_int (120)) (Prims.of_int (39)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
                         (Prims.of_int (121)) (Prims.of_int (20))
                         (Prims.of_int (131)) (Prims.of_int (26)))))
                (Obj.magic uu___2)
                (fun uu___3 ->
                   (fun g ->
                      let uu___3 =
                        FStar_Reflection_V2_Formula.term_as_formula g in
                      Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "FStar.Tactics.V2.Logic.fst"
                                    (Prims.of_int (121)) (Prims.of_int (26))
                                    (Prims.of_int (121)) (Prims.of_int (43)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "FStar.Tactics.V2.Logic.fst"
                                    (Prims.of_int (121)) (Prims.of_int (20))
                                    (Prims.of_int (131)) (Prims.of_int (26)))))
                           (Obj.magic uu___3)
                           (fun uu___4 ->
                              (fun uu___4 ->
                                 match uu___4 with
                                 | FStar_Reflection_V2_Formula.Forall
                                     (_b, _sort, _phi) ->
                                     Obj.magic
                                       (Obj.repr
                                          (let uu___5 = forall_intros () in
                                           FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "FStar.Tactics.V2.Logic.fst"
                                                      (Prims.of_int (123))
                                                      (Prims.of_int (38))
                                                      (Prims.of_int (123))
                                                      (Prims.of_int (54)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "FStar.Tactics.V2.Logic.fst"
                                                      (Prims.of_int (124))
                                                      (Prims.of_int (24))
                                                      (Prims.of_int (124))
                                                      (Prims.of_int (87)))))
                                             (Obj.magic uu___5)
                                             (fun uu___6 ->
                                                (fun binders ->
                                                   Obj.magic
                                                     (FStar_Tactics_V2_Derived.seq
                                                        (fun uu___6 ->
                                                           visit callback)
                                                        (fun uu___6 ->
                                                           l_revert_all
                                                             binders)))
                                                  uu___6)))
                                 | FStar_Reflection_V2_Formula.And (p, q) ->
                                     Obj.magic
                                       (Obj.repr
                                          (FStar_Tactics_V2_Derived.seq split
                                             (fun uu___5 -> visit callback)))
                                 | FStar_Reflection_V2_Formula.Implies 
                                     (p, q) ->
                                     Obj.magic
                                       (Obj.repr
                                          (let uu___5 = implies_intro () in
                                           FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "FStar.Tactics.V2.Logic.fst"
                                                      (Prims.of_int (128))
                                                      (Prims.of_int (32))
                                                      (Prims.of_int (128))
                                                      (Prims.of_int (48)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "FStar.Tactics.V2.Logic.fst"
                                                      (Prims.of_int (129))
                                                      (Prims.of_int (24))
                                                      (Prims.of_int (129))
                                                      (Prims.of_int (63)))))
                                             (Obj.magic uu___5)
                                             (fun uu___6 ->
                                                (fun uu___6 ->
                                                   Obj.magic
                                                     (FStar_Tactics_V2_Derived.seq
                                                        (fun uu___7 ->
                                                           visit callback)
                                                        l_revert)) uu___6)))
                                 | uu___5 ->
                                     Obj.magic
                                       (Obj.repr
                                          (FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___6 -> ())))) uu___4)))
                     uu___3)))
let rec (simplify_eq_implication :
  unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    let uu___1 = FStar_Tactics_V2_Derived.cur_env () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
               (Prims.of_int (136)) (Prims.of_int (12)) (Prims.of_int (136))
               (Prims.of_int (22)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
               (Prims.of_int (136)) (Prims.of_int (25)) (Prims.of_int (146))
               (Prims.of_int (37))))) (Obj.magic uu___1)
      (fun uu___2 ->
         (fun e ->
            let uu___2 = FStar_Tactics_V2_Derived.cur_goal () in
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
                          (Prims.of_int (137)) (Prims.of_int (12))
                          (Prims.of_int (137)) (Prims.of_int (23)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
                          (Prims.of_int (137)) (Prims.of_int (26))
                          (Prims.of_int (146)) (Prims.of_int (37)))))
                 (Obj.magic uu___2)
                 (fun uu___3 ->
                    (fun g ->
                       let uu___3 =
                         FStar_Tactics_V2_Derived.destruct_equality_implication
                           g in
                       Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.V2.Logic.fst"
                                     (Prims.of_int (138)) (Prims.of_int (12))
                                     (Prims.of_int (138)) (Prims.of_int (43)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.V2.Logic.fst"
                                     (Prims.of_int (139)) (Prims.of_int (4))
                                     (Prims.of_int (146)) (Prims.of_int (37)))))
                            (Obj.magic uu___3)
                            (fun uu___4 ->
                               (fun r ->
                                  match r with
                                  | FStar_Pervasives_Native.None ->
                                      Obj.magic
                                        (Obj.repr
                                           (FStar_Tactics_V2_Derived.fail
                                              "Not an equality implication"))
                                  | FStar_Pervasives_Native.Some
                                      (uu___4, rhs) ->
                                      Obj.magic
                                        (Obj.repr
                                           (let uu___5 = implies_intro () in
                                            FStar_Tactics_Effect.tac_bind
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "FStar.Tactics.V2.Logic.fst"
                                                       (Prims.of_int (143))
                                                       (Prims.of_int (19))
                                                       (Prims.of_int (143))
                                                       (Prims.of_int (35)))))
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "FStar.Tactics.V2.Logic.fst"
                                                       (Prims.of_int (144))
                                                       (Prims.of_int (8))
                                                       (Prims.of_int (146))
                                                       (Prims.of_int (37)))))
                                              (Obj.magic uu___5)
                                              (fun uu___6 ->
                                                 (fun eq_h ->
                                                    let uu___6 =
                                                      FStarC_Tactics_V2_Builtins.rewrite
                                                        eq_h in
                                                    Obj.magic
                                                      (FStar_Tactics_Effect.tac_bind
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "FStar.Tactics.V2.Logic.fst"
                                                                  (Prims.of_int (144))
                                                                  (Prims.of_int (8))
                                                                  (Prims.of_int (144))
                                                                  (Prims.of_int (20)))))
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "FStar.Tactics.V2.Logic.fst"
                                                                  (Prims.of_int (145))
                                                                  (Prims.of_int (8))
                                                                  (Prims.of_int (146))
                                                                  (Prims.of_int (37)))))
                                                         (Obj.magic uu___6)
                                                         (fun uu___7 ->
                                                            (fun uu___7 ->
                                                               let uu___8 =
                                                                 FStarC_Tactics_V2_Builtins.clear_top
                                                                   () in
                                                               Obj.magic
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Logic.fst"
                                                                    (Prims.of_int (145))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (145))
                                                                    (Prims.of_int (20)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Logic.fst"
                                                                    (Prims.of_int (146))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (146))
                                                                    (Prims.of_int (37)))))
                                                                    (
                                                                    Obj.magic
                                                                    uu___8)
                                                                    (
                                                                    fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    Obj.magic
                                                                    (visit
                                                                    simplify_eq_implication))
                                                                    uu___9)))
                                                              uu___7)))
                                                   uu___6)))) uu___4)))
                      uu___3))) uu___2)
let _ =
  FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.V2.Logic.simplify_eq_implication" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.V2.Logic.simplify_eq_implication (plugin)"
               (FStarC_Tactics_Native.from_tactic_1 simplify_eq_implication)
               FStarC_Syntax_Embeddings.e_unit
               FStarC_Syntax_Embeddings.e_unit psc ncb us args)
let (rewrite_all_equalities :
  unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ -> visit simplify_eq_implication
let _ =
  FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.V2.Logic.rewrite_all_equalities" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.V2.Logic.rewrite_all_equalities (plugin)"
               (FStarC_Tactics_Native.from_tactic_1 rewrite_all_equalities)
               FStarC_Syntax_Embeddings.e_unit
               FStarC_Syntax_Embeddings.e_unit psc ncb us args)
let rec (unfold_definition_and_simplify_eq :
  FStar_Tactics_NamedView.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun tm ->
    let uu___ = FStar_Tactics_V2_Derived.cur_goal () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
               (Prims.of_int (152)) (Prims.of_int (12)) (Prims.of_int (152))
               (Prims.of_int (23)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
               (Prims.of_int (153)) (Prims.of_int (4)) (Prims.of_int (167))
               (Prims.of_int (11))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun g ->
            let uu___1 = FStar_Reflection_V2_Formula.term_as_formula g in
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
                          (Prims.of_int (153)) (Prims.of_int (10))
                          (Prims.of_int (153)) (Prims.of_int (27)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
                          (Prims.of_int (153)) (Prims.of_int (4))
                          (Prims.of_int (167)) (Prims.of_int (11)))))
                 (Obj.magic uu___1)
                 (fun uu___2 ->
                    (fun uu___2 ->
                       match uu___2 with
                       | FStar_Reflection_V2_Formula.App (hd, arg) ->
                           Obj.magic
                             (Obj.repr
                                (if term_eq hd tm
                                 then
                                   Obj.repr
                                     (FStar_Tactics_V2_Derived.trivial ())
                                 else
                                   Obj.repr
                                     (FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___4 -> ()))))
                       | uu___3 ->
                           Obj.magic
                             (Obj.repr
                                (let uu___4 =
                                   FStar_Tactics_V2_Derived.destruct_equality_implication
                                     g in
                                 FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "FStar.Tactics.V2.Logic.fst"
                                            (Prims.of_int (159))
                                            (Prims.of_int (16))
                                            (Prims.of_int (159))
                                            (Prims.of_int (47)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "FStar.Tactics.V2.Logic.fst"
                                            (Prims.of_int (160))
                                            (Prims.of_int (8))
                                            (Prims.of_int (166))
                                            (Prims.of_int (66)))))
                                   (Obj.magic uu___4)
                                   (fun uu___5 ->
                                      (fun r ->
                                         match r with
                                         | FStar_Pervasives_Native.None ->
                                             Obj.magic
                                               (Obj.repr
                                                  (FStar_Tactics_V2_Derived.fail
                                                     "Not an equality implication"))
                                         | FStar_Pervasives_Native.Some
                                             (uu___5, rhs) ->
                                             Obj.magic
                                               (Obj.repr
                                                  (let uu___6 =
                                                     implies_intro () in
                                                   FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "FStar.Tactics.V2.Logic.fst"
                                                              (Prims.of_int (163))
                                                              (Prims.of_int (23))
                                                              (Prims.of_int (163))
                                                              (Prims.of_int (39)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "FStar.Tactics.V2.Logic.fst"
                                                              (Prims.of_int (164))
                                                              (Prims.of_int (12))
                                                              (Prims.of_int (166))
                                                              (Prims.of_int (66)))))
                                                     (Obj.magic uu___6)
                                                     (fun uu___7 ->
                                                        (fun eq_h ->
                                                           let uu___7 =
                                                             FStarC_Tactics_V2_Builtins.rewrite
                                                               eq_h in
                                                           Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Logic.fst"
                                                                    (Prims.of_int (164))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (164))
                                                                    (Prims.of_int (24)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Logic.fst"
                                                                    (Prims.of_int (165))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (166))
                                                                    (Prims.of_int (66)))))
                                                                (Obj.magic
                                                                   uu___7)
                                                                (fun uu___8
                                                                   ->
                                                                   (fun
                                                                    uu___8 ->
                                                                    let uu___9
                                                                    =
                                                                    FStarC_Tactics_V2_Builtins.clear_top
                                                                    () in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Logic.fst"
                                                                    (Prims.of_int (165))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (165))
                                                                    (Prims.of_int (24)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Logic.fst"
                                                                    (Prims.of_int (166))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (166))
                                                                    (Prims.of_int (66)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    Obj.magic
                                                                    (visit
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    unfold_definition_and_simplify_eq
                                                                    tm)))
                                                                    uu___10)))
                                                                    uu___8)))
                                                          uu___7)))) uu___5))))
                      uu___2))) uu___1)
let _ =
  FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.V2.Logic.unfold_definition_and_simplify_eq"
    (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.V2.Logic.unfold_definition_and_simplify_eq (plugin)"
               (FStarC_Tactics_Native.from_tactic_1
                  unfold_definition_and_simplify_eq)
               FStarC_Reflection_V2_Embeddings.e_term
               FStarC_Syntax_Embeddings.e_unit psc ncb us args)
let (unsquash :
  FStar_Tactics_NamedView.term ->
    (FStar_Tactics_NamedView.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    let uu___ =
      Obj.magic
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___1 ->
              FStarC_Reflection_V2_Builtins.pack_ln
                (FStarC_Reflection_V2_Data.Tv_FVar
                   (FStarC_Reflection_V2_Builtins.pack_fv
                      ["FStar"; "Tactics"; "V1"; "Logic"; "Lemmas"; "vbind"])))) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
               (Prims.of_int (182)) (Prims.of_int (12)) (Prims.of_int (182))
               (Prims.of_int (18)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
               (Prims.of_int (183)) (Prims.of_int (4)) (Prims.of_int (185))
               (Prims.of_int (19))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun v ->
            let uu___1 =
              FStar_Tactics_V2_Derived.apply_lemma
                (FStar_Reflection_V2_Derived.mk_e_app v [t]) in
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
                          (Prims.of_int (183)) (Prims.of_int (4))
                          (Prims.of_int (183)) (Prims.of_int (32)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
                          (Prims.of_int (183)) (Prims.of_int (33))
                          (Prims.of_int (185)) (Prims.of_int (19)))))
                 (Obj.magic uu___1)
                 (fun uu___2 ->
                    (fun uu___2 ->
                       let uu___3 = FStarC_Tactics_V2_Builtins.intro () in
                       Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.V2.Logic.fst"
                                     (Prims.of_int (184)) (Prims.of_int (12))
                                     (Prims.of_int (184)) (Prims.of_int (20)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range "dummy"
                                     Prims.int_zero Prims.int_zero
                                     Prims.int_zero Prims.int_zero)))
                            (Obj.magic uu___3)
                            (fun b ->
                               FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___4 ->
                                    FStar_Tactics_NamedView.pack
                                      (FStar_Tactics_NamedView.Tv_Var
                                         (FStar_Tactics_V2_SyntaxCoercions.binding_to_namedv
                                            b)))))) uu___2))) uu___1)
let _ =
  FStarC_Tactics_Native.register_tactic "FStar.Tactics.V2.Logic.unsquash"
    (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.V2.Logic.unsquash (plugin)"
               (FStarC_Tactics_Native.from_tactic_1 unsquash)
               FStarC_Reflection_V2_Embeddings.e_term
               FStarC_Reflection_V2_Embeddings.e_term psc ncb us args)
let (cases_or :
  FStar_Tactics_NamedView.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun o ->
    FStar_Tactics_V2_Derived.apply_lemma
      (FStar_Reflection_V2_Derived.mk_e_app
         (FStarC_Reflection_V2_Builtins.pack_ln
            (FStarC_Reflection_V2_Data.Tv_FVar
               (FStarC_Reflection_V2_Builtins.pack_fv
                  ["FStar"; "Tactics"; "V1"; "Logic"; "Lemmas"; "or_ind"])))
         [o])
let _ =
  FStarC_Tactics_Native.register_tactic "FStar.Tactics.V2.Logic.cases_or"
    (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.V2.Logic.cases_or (plugin)"
               (FStarC_Tactics_Native.from_tactic_1 cases_or)
               FStarC_Reflection_V2_Embeddings.e_term
               FStarC_Syntax_Embeddings.e_unit psc ncb us args)
let (cases_bool :
  FStar_Tactics_NamedView.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun b ->
    let uu___ =
      Obj.magic
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___1 ->
              FStarC_Reflection_V2_Builtins.pack_ln
                (FStarC_Reflection_V2_Data.Tv_FVar
                   (FStarC_Reflection_V2_Builtins.pack_fv
                      ["FStar";
                      "Tactics";
                      "V1";
                      "Logic";
                      "Lemmas";
                      "bool_ind"])))) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
               (Prims.of_int (191)) (Prims.of_int (13)) (Prims.of_int (191))
               (Prims.of_int (22)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
               (Prims.of_int (192)) (Prims.of_int (4)) (Prims.of_int (193))
               (Prims.of_int (104))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun bi ->
            Obj.magic
              (FStar_Tactics_V2_Derived.seq
                 (fun uu___1 ->
                    FStar_Tactics_V2_Derived.apply_lemma
                      (FStar_Reflection_V2_Derived.mk_e_app bi [b]))
                 (fun uu___1 ->
                    let uu___2 =
                      FStar_Tactics_V2_Derived.trytac
                        (fun uu___3 ->
                           let uu___4 = implies_intro () in
                           FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "FStar.Tactics.V2.Logic.fst"
                                      (Prims.of_int (193))
                                      (Prims.of_int (53))
                                      (Prims.of_int (193))
                                      (Prims.of_int (69)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "FStar.Tactics.V2.Logic.fst"
                                      (Prims.of_int (193))
                                      (Prims.of_int (73))
                                      (Prims.of_int (193))
                                      (Prims.of_int (96)))))
                             (Obj.magic uu___4)
                             (fun uu___5 ->
                                (fun b1 ->
                                   let uu___5 =
                                     FStarC_Tactics_V2_Builtins.rewrite b1 in
                                   Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "FStar.Tactics.V2.Logic.fst"
                                                 (Prims.of_int (193))
                                                 (Prims.of_int (73))
                                                 (Prims.of_int (193))
                                                 (Prims.of_int (82)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "FStar.Tactics.V2.Logic.fst"
                                                 (Prims.of_int (193))
                                                 (Prims.of_int (84))
                                                 (Prims.of_int (193))
                                                 (Prims.of_int (96)))))
                                        (Obj.magic uu___5)
                                        (fun uu___6 ->
                                           (fun uu___6 ->
                                              Obj.magic
                                                (FStarC_Tactics_V2_Builtins.clear_top
                                                   ())) uu___6))) uu___5)) in
                    FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range
                               "FStar.Tactics.V2.Logic.fst"
                               (Prims.of_int (193)) (Prims.of_int (27))
                               (Prims.of_int (193)) (Prims.of_int (97)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range
                               "FStar.Tactics.V2.Logic.fst"
                               (Prims.of_int (193)) (Prims.of_int (101))
                               (Prims.of_int (193)) (Prims.of_int (103)))))
                      (Obj.magic uu___2)
                      (fun uu___3 ->
                         FStar_Tactics_Effect.lift_div_tac (fun uu___4 -> ())))))
           uu___1)
let _ =
  FStarC_Tactics_Native.register_tactic "FStar.Tactics.V2.Logic.cases_bool"
    (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.V2.Logic.cases_bool (plugin)"
               (FStarC_Tactics_Native.from_tactic_1 cases_bool)
               FStarC_Reflection_V2_Embeddings.e_term
               FStarC_Syntax_Embeddings.e_unit psc ncb us args)
let (left : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_V2_Derived.apply_lemma
      (FStarC_Reflection_V2_Builtins.pack_ln
         (FStarC_Reflection_V2_Data.Tv_FVar
            (FStarC_Reflection_V2_Builtins.pack_fv
               ["FStar"; "Tactics"; "V1"; "Logic"; "Lemmas"; "or_intro_1"])))
let _ =
  FStarC_Tactics_Native.register_tactic "FStar.Tactics.V2.Logic.left"
    (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.V2.Logic.left (plugin)"
               (FStarC_Tactics_Native.from_tactic_1 left)
               FStarC_Syntax_Embeddings.e_unit
               FStarC_Syntax_Embeddings.e_unit psc ncb us args)
let (right : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_V2_Derived.apply_lemma
      (FStarC_Reflection_V2_Builtins.pack_ln
         (FStarC_Reflection_V2_Data.Tv_FVar
            (FStarC_Reflection_V2_Builtins.pack_fv
               ["FStar"; "Tactics"; "V1"; "Logic"; "Lemmas"; "or_intro_2"])))
let _ =
  FStarC_Tactics_Native.register_tactic "FStar.Tactics.V2.Logic.right"
    (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.V2.Logic.right (plugin)"
               (FStarC_Tactics_Native.from_tactic_1 right)
               FStarC_Syntax_Embeddings.e_unit
               FStarC_Syntax_Embeddings.e_unit psc ncb us args)
let (and_elim :
  FStar_Tactics_NamedView.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    FStar_Tactics_V2_Derived.try_with
      (fun uu___ ->
         match () with
         | () ->
             FStar_Tactics_V2_Derived.apply_lemma
               (FStarC_Reflection_V2_Builtins.pack_ln
                  (FStarC_Reflection_V2_Data.Tv_App
                     ((FStarC_Reflection_V2_Builtins.pack_ln
                         (FStarC_Reflection_V2_Data.Tv_FVar
                            (FStarC_Reflection_V2_Builtins.pack_fv
                               ["FStar";
                               "Tactics";
                               "V1";
                               "Logic";
                               "Lemmas";
                               "__and_elim"]))),
                       (t, FStarC_Reflection_V2_Data.Q_Explicit)))))
      (fun uu___ ->
         FStar_Tactics_V2_Derived.apply_lemma
           (FStarC_Reflection_V2_Builtins.pack_ln
              (FStarC_Reflection_V2_Data.Tv_App
                 ((FStarC_Reflection_V2_Builtins.pack_ln
                     (FStarC_Reflection_V2_Data.Tv_FVar
                        (FStarC_Reflection_V2_Builtins.pack_fv
                           ["FStar";
                           "Tactics";
                           "V1";
                           "Logic";
                           "Lemmas";
                           "__and_elim'"]))),
                   (t, FStarC_Reflection_V2_Data.Q_Explicit)))))
let _ =
  FStarC_Tactics_Native.register_tactic "FStar.Tactics.V2.Logic.and_elim"
    (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.V2.Logic.and_elim (plugin)"
               (FStarC_Tactics_Native.from_tactic_1 and_elim)
               FStarC_Reflection_V2_Embeddings.e_term
               FStarC_Syntax_Embeddings.e_unit psc ncb us args)
let (destruct_and :
  FStar_Tactics_NamedView.term ->
    ((FStar_Tactics_NamedView.binding * FStar_Tactics_NamedView.binding),
      unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    let uu___ = and_elim t in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
               (Prims.of_int (208)) (Prims.of_int (4)) (Prims.of_int (208))
               (Prims.of_int (14)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
               (Prims.of_int (209)) (Prims.of_int (4)) (Prims.of_int (209))
               (Prims.of_int (40))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun uu___1 ->
            let uu___2 = implies_intro () in
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
                          (Prims.of_int (209)) (Prims.of_int (5))
                          (Prims.of_int (209)) (Prims.of_int (21)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
                          (Prims.of_int (209)) (Prims.of_int (4))
                          (Prims.of_int (209)) (Prims.of_int (40)))))
                 (Obj.magic uu___2)
                 (fun uu___3 ->
                    (fun uu___3 ->
                       let uu___4 = implies_intro () in
                       Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.V2.Logic.fst"
                                     (Prims.of_int (209)) (Prims.of_int (23))
                                     (Prims.of_int (209)) (Prims.of_int (39)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.V2.Logic.fst"
                                     (Prims.of_int (209)) (Prims.of_int (4))
                                     (Prims.of_int (209)) (Prims.of_int (40)))))
                            (Obj.magic uu___4)
                            (fun uu___5 ->
                               FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___6 -> (uu___3, uu___5))))) uu___3)))
           uu___1)
let _ =
  FStarC_Tactics_Native.register_tactic "FStar.Tactics.V2.Logic.destruct_and"
    (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.V2.Logic.destruct_and (plugin)"
               (FStarC_Tactics_Native.from_tactic_1 destruct_and)
               FStarC_Reflection_V2_Embeddings.e_term
               (FStarC_Syntax_Embeddings.e_tuple2
                  FStarC_Reflection_V2_Embeddings.e_binding
                  FStarC_Reflection_V2_Embeddings.e_binding) psc ncb us args)
let (witness :
  FStar_Tactics_NamedView.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    let uu___ =
      FStar_Tactics_V2_Derived.apply_raw
        (FStarC_Reflection_V2_Builtins.pack_ln
           (FStarC_Reflection_V2_Data.Tv_FVar
              (FStarC_Reflection_V2_Builtins.pack_fv
                 ["FStar"; "Tactics"; "V1"; "Logic"; "Lemmas"; "__witness"]))) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
               (Prims.of_int (212)) (Prims.of_int (4)) (Prims.of_int (212))
               (Prims.of_int (26)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
               (Prims.of_int (213)) (Prims.of_int (4)) (Prims.of_int (213))
               (Prims.of_int (11))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun uu___1 -> Obj.magic (FStar_Tactics_V2_Derived.exact t)) uu___1)
let _ =
  FStarC_Tactics_Native.register_tactic "FStar.Tactics.V2.Logic.witness"
    (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.V2.Logic.witness (plugin)"
               (FStarC_Tactics_Native.from_tactic_1 witness)
               FStarC_Reflection_V2_Embeddings.e_term
               FStarC_Syntax_Embeddings.e_unit psc ncb us args)
let (elim_exists :
  FStar_Tactics_NamedView.term ->
    ((FStar_Tactics_NamedView.binding * FStar_Tactics_NamedView.binding),
      unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    let uu___ =
      FStar_Tactics_V2_Derived.apply_lemma
        (FStarC_Reflection_V2_Builtins.pack_ln
           (FStarC_Reflection_V2_Data.Tv_App
              ((FStarC_Reflection_V2_Builtins.pack_ln
                  (FStarC_Reflection_V2_Data.Tv_FVar
                     (FStarC_Reflection_V2_Builtins.pack_fv
                        ["FStar";
                        "Tactics";
                        "V1";
                        "Logic";
                        "Lemmas";
                        "__elim_exists'"]))),
                (t, FStarC_Reflection_V2_Data.Q_Explicit)))) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
               (Prims.of_int (217)) (Prims.of_int (2)) (Prims.of_int (217))
               (Prims.of_int (41)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
               (Prims.of_int (217)) (Prims.of_int (42)) (Prims.of_int (220))
               (Prims.of_int (9))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun uu___1 ->
            let uu___2 = FStarC_Tactics_V2_Builtins.intro () in
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
                          (Prims.of_int (218)) (Prims.of_int (10))
                          (Prims.of_int (218)) (Prims.of_int (18)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
                          (Prims.of_int (218)) (Prims.of_int (21))
                          (Prims.of_int (220)) (Prims.of_int (9)))))
                 (Obj.magic uu___2)
                 (fun uu___3 ->
                    (fun x ->
                       let uu___3 = FStarC_Tactics_V2_Builtins.intro () in
                       Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.V2.Logic.fst"
                                     (Prims.of_int (219)) (Prims.of_int (11))
                                     (Prims.of_int (219)) (Prims.of_int (19)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.V2.Logic.fst"
                                     (Prims.of_int (220)) (Prims.of_int (2))
                                     (Prims.of_int (220)) (Prims.of_int (9)))))
                            (Obj.magic uu___3)
                            (fun pf ->
                               FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___4 -> (x, pf))))) uu___3))) uu___1)
let _ =
  FStarC_Tactics_Native.register_tactic "FStar.Tactics.V2.Logic.elim_exists"
    (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.V2.Logic.elim_exists (plugin)"
               (FStarC_Tactics_Native.from_tactic_1 elim_exists)
               FStarC_Reflection_V2_Embeddings.e_term
               (FStarC_Syntax_Embeddings.e_tuple2
                  FStarC_Reflection_V2_Embeddings.e_binding
                  FStarC_Reflection_V2_Embeddings.e_binding) psc ncb us args)
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
                 (FStarC_Reflection_V2_Builtins.pack_ln
                    (FStarC_Reflection_V2_Data.Tv_App
                       ((FStarC_Reflection_V2_Builtins.pack_ln
                           (FStarC_Reflection_V2_Data.Tv_App
                              ((FStarC_Reflection_V2_Builtins.pack_ln
                                  (FStarC_Reflection_V2_Data.Tv_FVar
                                     (FStarC_Reflection_V2_Builtins.pack_fv
                                        ["FStar";
                                        "Tactics";
                                        "V1";
                                        "Logic";
                                        "Lemmas";
                                        "__forall_inst_sq"]))),
                                (fa, FStarC_Reflection_V2_Data.Q_Explicit)))),
                         (x, FStarC_Reflection_V2_Data.Q_Explicit)))))
        (fun uu___ ->
           FStar_Tactics_V2_Derived.try_with
             (fun uu___1 ->
                match () with
                | () ->
                    FStar_Tactics_V2_Derived.pose
                      (FStarC_Reflection_V2_Builtins.pack_ln
                         (FStarC_Reflection_V2_Data.Tv_App
                            ((FStarC_Reflection_V2_Builtins.pack_ln
                                (FStarC_Reflection_V2_Data.Tv_App
                                   ((FStarC_Reflection_V2_Builtins.pack_ln
                                       (FStarC_Reflection_V2_Data.Tv_FVar
                                          (FStarC_Reflection_V2_Builtins.pack_fv
                                             ["FStar";
                                             "Tactics";
                                             "V1";
                                             "Logic";
                                             "Lemmas";
                                             "__forall_inst"]))),
                                     (fa,
                                       FStarC_Reflection_V2_Data.Q_Explicit)))),
                              (x, FStarC_Reflection_V2_Data.Q_Explicit)))))
             (fun uu___1 ->
                (fun uu___1 ->
                   Obj.magic
                     (FStar_Tactics_V2_Derived.fail "could not instantiate"))
                  uu___1))
let _ =
  FStarC_Tactics_Native.register_tactic "FStar.Tactics.V2.Logic.instantiate"
    (Prims.of_int (3))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_2
               "FStar.Tactics.V2.Logic.instantiate (plugin)"
               (FStarC_Tactics_Native.from_tactic_2 instantiate)
               FStarC_Reflection_V2_Embeddings.e_term
               FStarC_Reflection_V2_Embeddings.e_term
               FStarC_Reflection_V2_Embeddings.e_binding psc ncb us args)
let (instantiate_as :
  FStar_Tactics_NamedView.term ->
    FStar_Tactics_NamedView.term ->
      Prims.string ->
        (FStar_Tactics_NamedView.binding, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun fa ->
    fun x ->
      fun s ->
        let uu___ = instantiate fa x in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
                   (Prims.of_int (228)) (Prims.of_int (12))
                   (Prims.of_int (228)) (Prims.of_int (28)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
                   (Prims.of_int (229)) (Prims.of_int (4))
                   (Prims.of_int (229)) (Prims.of_int (17)))))
          (Obj.magic uu___)
          (fun uu___1 ->
             (fun b -> Obj.magic (FStarC_Tactics_V2_Builtins.rename_to b s))
               uu___1)
let _ =
  FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.V2.Logic.instantiate_as" (Prims.of_int (4))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_3
               "FStar.Tactics.V2.Logic.instantiate_as (plugin)"
               (FStarC_Tactics_Native.from_tactic_3 instantiate_as)
               FStarC_Reflection_V2_Embeddings.e_term
               FStarC_Reflection_V2_Embeddings.e_term
               FStarC_Syntax_Embeddings.e_string
               FStarC_Reflection_V2_Embeddings.e_binding psc ncb us args)
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
                    let uu___2 =
                      FStar_Tactics_V2_Derived.apply_lemma
                        (FStarC_Reflection_V2_Builtins.pack_ln
                           (FStarC_Reflection_V2_Data.Tv_App
                              ((FStarC_Reflection_V2_Builtins.pack_ln
                                  (FStarC_Reflection_V2_Data.Tv_FVar
                                     (FStarC_Reflection_V2_Builtins.pack_fv
                                        ["FStar";
                                        "Tactics";
                                        "V1";
                                        "Logic";
                                        "Lemmas";
                                        "sklem0"]))),
                                ((FStar_Tactics_V2_SyntaxCoercions.binding_to_term
                                    b), FStarC_Reflection_V2_Data.Q_Explicit)))) in
                    FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range
                               "FStar.Tactics.V2.Logic.fst"
                               (Prims.of_int (234)) (Prims.of_int (6))
                               (Prims.of_int (234)) (Prims.of_int (35)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range
                               "FStar.Tactics.V2.Logic.fst"
                               (Prims.of_int (235)) (Prims.of_int (6))
                               (Prims.of_int (239)) (Prims.of_int (29)))))
                      (Obj.magic uu___2)
                      (fun uu___3 ->
                         (fun uu___3 ->
                            let uu___4 =
                              let uu___5 =
                                let uu___6 =
                                  FStar_Tactics_V2_Derived.ngoals () in
                                FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "FStar.Tactics.V2.Logic.fst"
                                           (Prims.of_int (235))
                                           (Prims.of_int (9))
                                           (Prims.of_int (235))
                                           (Prims.of_int (18)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "FStar.Tactics.V2.Logic.fst"
                                           (Prims.of_int (235))
                                           (Prims.of_int (9))
                                           (Prims.of_int (235))
                                           (Prims.of_int (23)))))
                                  (Obj.magic uu___6)
                                  (fun uu___7 ->
                                     FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___8 -> uu___7 <> Prims.int_one)) in
                              FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.V2.Logic.fst"
                                         (Prims.of_int (235))
                                         (Prims.of_int (9))
                                         (Prims.of_int (235))
                                         (Prims.of_int (23)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.V2.Logic.fst"
                                         (Prims.of_int (235))
                                         (Prims.of_int (6))
                                         (Prims.of_int (235))
                                         (Prims.of_int (38)))))
                                (Obj.magic uu___5)
                                (fun uu___6 ->
                                   if uu___6
                                   then FStar_Tactics_V2_Derived.fail "no"
                                   else
                                     FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___8 -> ())) in
                            Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "FStar.Tactics.V2.Logic.fst"
                                          (Prims.of_int (235))
                                          (Prims.of_int (6))
                                          (Prims.of_int (235))
                                          (Prims.of_int (38)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "FStar.Tactics.V2.Logic.fst"
                                          (Prims.of_int (236))
                                          (Prims.of_int (6))
                                          (Prims.of_int (239))
                                          (Prims.of_int (29)))))
                                 (Obj.magic uu___4)
                                 (fun uu___5 ->
                                    (fun uu___5 ->
                                       let uu___6 =
                                         FStarC_Tactics_V2_Builtins.clear b in
                                       Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "FStar.Tactics.V2.Logic.fst"
                                                     (Prims.of_int (236))
                                                     (Prims.of_int (6))
                                                     (Prims.of_int (236))
                                                     (Prims.of_int (13)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "FStar.Tactics.V2.Logic.fst"
                                                     (Prims.of_int (236))
                                                     (Prims.of_int (14))
                                                     (Prims.of_int (239))
                                                     (Prims.of_int (29)))))
                                            (Obj.magic uu___6)
                                            (fun uu___7 ->
                                               (fun uu___7 ->
                                                  let uu___8 =
                                                    forall_intro () in
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "FStar.Tactics.V2.Logic.fst"
                                                                (Prims.of_int (237))
                                                                (Prims.of_int (15))
                                                                (Prims.of_int (237))
                                                                (Prims.of_int (30)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "FStar.Tactics.V2.Logic.fst"
                                                                (Prims.of_int (237))
                                                                (Prims.of_int (33))
                                                                (Prims.of_int (239))
                                                                (Prims.of_int (29)))))
                                                       (Obj.magic uu___8)
                                                       (fun uu___9 ->
                                                          (fun bx ->
                                                             let uu___9 =
                                                               implies_intro
                                                                 () in
                                                             Obj.magic
                                                               (FStar_Tactics_Effect.tac_bind
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Logic.fst"
                                                                    (Prims.of_int (238))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (238))
                                                                    (Prims.of_int (31)))))
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.V2.Logic.fst"
                                                                    (Prims.of_int (239))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (239))
                                                                    (Prims.of_int (29)))))
                                                                  (Obj.magic
                                                                    uu___9)
                                                                  (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun b'
                                                                    ->
                                                                    Obj.magic
                                                                    (sk_binder'
                                                                    (bx ::
                                                                    acc) b'))
                                                                    uu___10)))
                                                            uu___9))) uu___7)))
                                      uu___5))) uu___3))
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
    let uu___1 =
      let uu___2 = FStar_Tactics_V2_Derived.cur_env () in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
                 (Prims.of_int (248)) (Prims.of_int (23))
                 (Prims.of_int (248)) (Prims.of_int (35)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
                 (Prims.of_int (248)) (Prims.of_int (11))
                 (Prims.of_int (248)) (Prims.of_int (35)))))
        (Obj.magic uu___2)
        (fun uu___3 ->
           FStar_Tactics_Effect.lift_div_tac
             (fun uu___4 -> FStarC_Reflection_V2_Builtins.vars_of_env uu___3)) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
               (Prims.of_int (248)) (Prims.of_int (11)) (Prims.of_int (248))
               (Prims.of_int (35)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
               (Prims.of_int (249)) (Prims.of_int (2)) (Prims.of_int (249))
               (Prims.of_int (18))))) (Obj.magic uu___1)
      (fun uu___2 ->
         (fun bs -> Obj.magic (FStar_Tactics_Util.map sk_binder bs)) uu___2)
let _ =
  FStarC_Tactics_Native.register_tactic "FStar.Tactics.V2.Logic.skolem"
    (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.V2.Logic.skolem (plugin)"
               (FStarC_Tactics_Native.from_tactic_1 skolem)
               FStarC_Syntax_Embeddings.e_unit
               (FStarC_Syntax_Embeddings.e_list
                  (FStarC_Syntax_Embeddings.e_tuple2
                     (FStarC_Syntax_Embeddings.e_list
                        FStarC_Reflection_V2_Embeddings.e_binding)
                     FStarC_Reflection_V2_Embeddings.e_binding)) psc ncb us
               args)
let (easy_fill : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    let uu___1 =
      FStar_Tactics_V2_Derived.repeat FStarC_Tactics_V2_Builtins.intro in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
               (Prims.of_int (252)) (Prims.of_int (12)) (Prims.of_int (252))
               (Prims.of_int (24)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
               (Prims.of_int (252)) (Prims.of_int (27)) (Prims.of_int (255))
               (Prims.of_int (10))))) (Obj.magic uu___1)
      (fun uu___2 ->
         (fun uu___2 ->
            let uu___3 =
              FStar_Tactics_V2_Derived.trytac
                (fun uu___4 ->
                   let uu___5 =
                     FStar_Tactics_V2_Derived.apply
                       (FStarC_Reflection_V2_Builtins.pack_ln
                          (FStarC_Reflection_V2_Data.Tv_FVar
                             (FStarC_Reflection_V2_Builtins.pack_fv
                                ["FStar";
                                "Tactics";
                                "V1";
                                "Logic";
                                "Lemmas";
                                "lemma_from_squash"]))) in
                   FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
                              (Prims.of_int (254)) (Prims.of_int (30))
                              (Prims.of_int (254)) (Prims.of_int (56)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
                              (Prims.of_int (254)) (Prims.of_int (58))
                              (Prims.of_int (254)) (Prims.of_int (66)))))
                     (Obj.magic uu___5)
                     (fun uu___6 ->
                        (fun uu___6 ->
                           Obj.magic (FStarC_Tactics_V2_Builtins.intro ()))
                          uu___6)) in
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
                          (Prims.of_int (254)) (Prims.of_int (12))
                          (Prims.of_int (254)) (Prims.of_int (67)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.V2.Logic.fst"
                          (Prims.of_int (255)) (Prims.of_int (4))
                          (Prims.of_int (255)) (Prims.of_int (10)))))
                 (Obj.magic uu___3)
                 (fun uu___4 ->
                    (fun uu___4 ->
                       Obj.magic (FStar_Tactics_V2_Derived.smt ())) uu___4)))
           uu___2)
let _ =
  FStarC_Tactics_Native.register_tactic "FStar.Tactics.V2.Logic.easy_fill"
    (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.V2.Logic.easy_fill (plugin)"
               (FStarC_Tactics_Native.from_tactic_1 easy_fill)
               FStarC_Syntax_Embeddings.e_unit
               FStarC_Syntax_Embeddings.e_unit psc ncb us args)
let easy : 'a . 'a -> 'a = fun x -> x
let _ =
  FStarC_Tactics_Native.register_plugin "FStar.Tactics.V2.Logic.easy"
    (Prims.of_int (2))
    (fun _psc ->
       fun cb ->
         fun us ->
           fun args ->
             FStarC_Syntax_Embeddings.debug_wrap
               "FStar.Tactics.V2.Logic.easy"
               (fun _ ->
                  match args with
                  | (tv_0, _)::args_tail ->
                      (FStarC_Syntax_Embeddings.arrow_as_prim_step_1
                         (FStarC_Syntax_Embeddings.mk_any_emb tv_0)
                         (FStarC_Syntax_Embeddings.mk_any_emb tv_0) easy
                         (FStarC_Ident.lid_of_str
                            "FStar.Tactics.V2.Logic.easy") cb us) args_tail
                  | _ -> failwith "arity mismatch"))
    (fun cb ->
       fun us ->
         fun args ->
           FStarC_Syntax_Embeddings.debug_wrap "FStar.Tactics.V2.Logic.easy"
             (fun _ ->
                match args with
                | (tv_0, _)::args_tail ->
                    (FStarC_TypeChecker_NBETerm.arrow_as_prim_step_1
                       (FStarC_TypeChecker_NBETerm.mk_any_emb tv_0)
                       (FStarC_TypeChecker_NBETerm.mk_any_emb tv_0) easy
                       (FStarC_Ident.lid_of_str "FStar.Tactics.V2.Logic.easy")
                       cb us) args_tail
                | _ -> failwith "arity mismatch"))
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
               (FStarC_Reflection_V2_Builtins.pack_ln
                  (FStarC_Reflection_V2_Data.Tv_App
                     ((FStarC_Reflection_V2_Builtins.pack_ln
                         (FStarC_Reflection_V2_Data.Tv_FVar
                            (FStarC_Reflection_V2_Builtins.pack_fv
                               ["FStar";
                               "Tactics";
                               "V1";
                               "Logic";
                               "Lemmas";
                               "lem1_fa"]))),
                       (t, FStarC_Reflection_V2_Data.Q_Explicit)))))
      (fun uu___ ->
         FStar_Tactics_V2_Derived.try_with
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
                                    "V1";
                                    "Logic";
                                    "Lemmas";
                                    "lem2_fa"]))),
                            (t, FStarC_Reflection_V2_Data.Q_Explicit)))))
           (fun uu___1 ->
              FStar_Tactics_V2_Derived.try_with
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
                                         "V1";
                                         "Logic";
                                         "Lemmas";
                                         "lem3_fa"]))),
                                 (t, FStarC_Reflection_V2_Data.Q_Explicit)))))
                (fun uu___2 ->
                   (fun uu___2 ->
                      Obj.magic
                        (FStar_Tactics_V2_Derived.fail
                           "using_lemma: failed to instantiate")) uu___2)))
let _ =
  FStarC_Tactics_Native.register_tactic "FStar.Tactics.V2.Logic.using_lemma"
    (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.V2.Logic.using_lemma (plugin)"
               (FStarC_Tactics_Native.from_tactic_1 using_lemma)
               FStarC_Reflection_V2_Embeddings.e_term
               FStarC_Reflection_V2_Embeddings.e_binding psc ncb us args)