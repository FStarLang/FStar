open Fstarcompiler
open Prims
let step (t : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) :
  (unit, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    FStar_Tactics_V2_Derived.apply_lemma
      (FStarC_Reflection_V2_Builtins.pack_ln
         (FStarC_Reflection_V2_Data.Tv_FVar
            (FStarC_Reflection_V2_Builtins.pack_fv
               ["FStar"; "Tactics"; "Canon"; "Lemmas"; "trans"]))) ps;
    t () ps
let step_lemma (lem : FStar_Tactics_NamedView.term) :
  (unit, unit) FStar_Tactics_Effect.tac_repr=
  step (fun uu___ -> FStar_Tactics_V2_Derived.apply_lemma lem)
let rec canon_point (e : FStar_Reflection_V2_Arith.expr) :
  (FStar_Reflection_V2_Arith.expr, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x uu___ ps1 = FStar_Tactics_V2_Derived.trefl () ps1; e in
    match e with
    | FStar_Reflection_V2_Arith.Plus
        (FStar_Reflection_V2_Arith.Lit a, FStar_Reflection_V2_Arith.Lit b) ->
        (FStarC_Tactics_V2_Builtins.norm
           [Fstarcompiler.FStarC_NormSteps.primops] ps;
         FStar_Tactics_V2_Derived.trefl () ps;
         FStar_Reflection_V2_Arith.Lit (a + b))
    | FStar_Reflection_V2_Arith.Mult
        (FStar_Reflection_V2_Arith.Lit a, FStar_Reflection_V2_Arith.Lit b) ->
        (FStarC_Tactics_V2_Builtins.norm
           [Fstarcompiler.FStarC_NormSteps.delta;
           Fstarcompiler.FStarC_NormSteps.primops] ps;
         FStar_Tactics_V2_Derived.trefl () ps;
         FStar_Reflection_V2_Arith.Lit (a * b))
    | FStar_Reflection_V2_Arith.Neg e1 ->
        (step_lemma
           (FStarC_Reflection_V2_Builtins.pack_ln
              (FStarC_Reflection_V2_Data.Tv_FVar
                 (FStarC_Reflection_V2_Builtins.pack_fv
                    ["FStar"; "Tactics"; "Canon"; "Lemmas"; "neg_minus_one"])))
           ps;
         canon_point
           (FStar_Reflection_V2_Arith.Mult
              ((FStar_Reflection_V2_Arith.Lit (Prims.of_int (-1))), e1)) ps)
    | FStar_Reflection_V2_Arith.Mult
        (a, FStar_Reflection_V2_Arith.Plus (b, c)) ->
        (step_lemma
           (FStarC_Reflection_V2_Builtins.pack_ln
              (FStarC_Reflection_V2_Data.Tv_FVar
                 (FStarC_Reflection_V2_Builtins.pack_fv
                    ["FStar"; "Tactics"; "Canon"; "Lemmas"; "distr"]))) ps;
         step_lemma
           (FStarC_Reflection_V2_Builtins.pack_ln
              (FStarC_Reflection_V2_Data.Tv_FVar
                 (FStarC_Reflection_V2_Builtins.pack_fv
                    ["FStar"; "Tactics"; "Canon"; "Lemmas"; "cong_plus"])))
           ps;
         (let x3 = canon_point (FStar_Reflection_V2_Arith.Mult (a, b)) ps in
          let x4 = canon_point (FStar_Reflection_V2_Arith.Mult (a, c)) ps in
          canon_point (FStar_Reflection_V2_Arith.Plus (x3, x4)) ps))
    | FStar_Reflection_V2_Arith.Mult
        (FStar_Reflection_V2_Arith.Plus (a, b), c) ->
        (step_lemma
           (FStarC_Reflection_V2_Builtins.pack_ln
              (FStarC_Reflection_V2_Data.Tv_FVar
                 (FStarC_Reflection_V2_Builtins.pack_fv
                    ["FStar"; "Tactics"; "Canon"; "Lemmas"; "distl"]))) ps;
         step_lemma
           (FStarC_Reflection_V2_Builtins.pack_ln
              (FStarC_Reflection_V2_Data.Tv_FVar
                 (FStarC_Reflection_V2_Builtins.pack_fv
                    ["FStar"; "Tactics"; "Canon"; "Lemmas"; "cong_plus"])))
           ps;
         (let x3 = canon_point (FStar_Reflection_V2_Arith.Mult (a, c)) ps in
          let x4 = canon_point (FStar_Reflection_V2_Arith.Mult (b, c)) ps in
          canon_point (FStar_Reflection_V2_Arith.Plus (x3, x4)) ps))
    | FStar_Reflection_V2_Arith.Mult
        (a, FStar_Reflection_V2_Arith.Mult (b, c)) ->
        (step_lemma
           (FStarC_Reflection_V2_Builtins.pack_ln
              (FStarC_Reflection_V2_Data.Tv_FVar
                 (FStarC_Reflection_V2_Builtins.pack_fv
                    ["FStar"; "Tactics"; "Canon"; "Lemmas"; "ass_mult_l"])))
           ps;
         step_lemma
           (FStarC_Reflection_V2_Builtins.pack_ln
              (FStarC_Reflection_V2_Data.Tv_FVar
                 (FStarC_Reflection_V2_Builtins.pack_fv
                    ["FStar"; "Tactics"; "Canon"; "Lemmas"; "cong_mult"])))
           ps;
         (let x3 = canon_point (FStar_Reflection_V2_Arith.Mult (a, b)) ps in
          let x4 = canon_point c ps in
          canon_point (FStar_Reflection_V2_Arith.Mult (x3, x4)) ps))
    | FStar_Reflection_V2_Arith.Plus
        (a, FStar_Reflection_V2_Arith.Plus (b, c)) ->
        (step_lemma
           (FStarC_Reflection_V2_Builtins.pack_ln
              (FStarC_Reflection_V2_Data.Tv_FVar
                 (FStarC_Reflection_V2_Builtins.pack_fv
                    ["FStar"; "Tactics"; "Canon"; "Lemmas"; "ass_plus_l"])))
           ps;
         step_lemma
           (FStarC_Reflection_V2_Builtins.pack_ln
              (FStarC_Reflection_V2_Data.Tv_FVar
                 (FStarC_Reflection_V2_Builtins.pack_fv
                    ["FStar"; "Tactics"; "Canon"; "Lemmas"; "cong_plus"])))
           ps;
         (let x3 = canon_point (FStar_Reflection_V2_Arith.Plus (a, b)) ps in
          let x4 = canon_point c ps in
          canon_point (FStar_Reflection_V2_Arith.Plus (x3, x4)) ps))
    | FStar_Reflection_V2_Arith.Plus
        (FStar_Reflection_V2_Arith.Plus (a, b), c) ->
        if FStar_Order.gt (FStar_Reflection_V2_Arith.compare_expr b c)
        then
          (step_lemma
             (FStarC_Reflection_V2_Builtins.pack_ln
                (FStarC_Reflection_V2_Data.Tv_FVar
                   (FStarC_Reflection_V2_Builtins.pack_fv
                      ["FStar"; "Tactics"; "Canon"; "Lemmas"; "sw_plus"])))
             ps;
           FStar_Tactics_V2_Derived.apply_lemma
             (FStarC_Reflection_V2_Builtins.pack_ln
                (FStarC_Reflection_V2_Data.Tv_FVar
                   (FStarC_Reflection_V2_Builtins.pack_fv
                      ["FStar"; "Tactics"; "Canon"; "Lemmas"; "cong_plus"])))
             ps;
           (let x3 = canon_point (FStar_Reflection_V2_Arith.Plus (a, c)) ps in
            FStar_Tactics_V2_Derived.trefl () ps;
            FStar_Reflection_V2_Arith.Plus (x3, b)))
        else x () ps
    | FStar_Reflection_V2_Arith.Mult
        (FStar_Reflection_V2_Arith.Mult (a, b), c) ->
        if FStar_Order.gt (FStar_Reflection_V2_Arith.compare_expr b c)
        then
          (step_lemma
             (FStarC_Reflection_V2_Builtins.pack_ln
                (FStarC_Reflection_V2_Data.Tv_FVar
                   (FStarC_Reflection_V2_Builtins.pack_fv
                      ["FStar"; "Tactics"; "Canon"; "Lemmas"; "sw_mult"])))
             ps;
           FStar_Tactics_V2_Derived.apply_lemma
             (FStarC_Reflection_V2_Builtins.pack_ln
                (FStarC_Reflection_V2_Data.Tv_FVar
                   (FStarC_Reflection_V2_Builtins.pack_fv
                      ["FStar"; "Tactics"; "Canon"; "Lemmas"; "cong_mult"])))
             ps;
           (let x3 = canon_point (FStar_Reflection_V2_Arith.Mult (a, c)) ps in
            FStar_Tactics_V2_Derived.trefl () ps;
            FStar_Reflection_V2_Arith.Mult (x3, b)))
        else x () ps
    | FStar_Reflection_V2_Arith.Plus (a, FStar_Reflection_V2_Arith.Lit uu___)
        when uu___ = Prims.int_zero ->
        (FStar_Tactics_V2_Derived.apply_lemma
           (FStarC_Reflection_V2_Builtins.pack_ln
              (FStarC_Reflection_V2_Data.Tv_FVar
                 (FStarC_Reflection_V2_Builtins.pack_fv
                    ["FStar"; "Tactics"; "Canon"; "Lemmas"; "x_plus_zero"])))
           ps;
         a)
    | FStar_Reflection_V2_Arith.Plus (FStar_Reflection_V2_Arith.Lit uu___, b)
        when uu___ = Prims.int_zero ->
        (FStar_Tactics_V2_Derived.apply_lemma
           (FStarC_Reflection_V2_Builtins.pack_ln
              (FStarC_Reflection_V2_Data.Tv_FVar
                 (FStarC_Reflection_V2_Builtins.pack_fv
                    ["FStar"; "Tactics"; "Canon"; "Lemmas"; "zero_plus_x"])))
           ps;
         b)
    | FStar_Reflection_V2_Arith.Plus (a, b) ->
        if FStar_Order.gt (FStar_Reflection_V2_Arith.compare_expr a b)
        then
          (FStar_Tactics_V2_Derived.apply_lemma
             (FStarC_Reflection_V2_Builtins.pack_ln
                (FStarC_Reflection_V2_Data.Tv_FVar
                   (FStarC_Reflection_V2_Builtins.pack_fv
                      ["FStar"; "Tactics"; "Canon"; "Lemmas"; "comm_plus"])))
             ps;
           FStar_Reflection_V2_Arith.Plus (b, a))
        else x () ps
    | FStar_Reflection_V2_Arith.Mult
        (FStar_Reflection_V2_Arith.Lit uu___, uu___1) when
        uu___ = Prims.int_zero ->
        (FStar_Tactics_V2_Derived.apply_lemma
           (FStarC_Reflection_V2_Builtins.pack_ln
              (FStarC_Reflection_V2_Data.Tv_FVar
                 (FStarC_Reflection_V2_Builtins.pack_fv
                    ["FStar"; "Tactics"; "Canon"; "Lemmas"; "zero_mult_x"])))
           ps;
         FStar_Reflection_V2_Arith.Lit Prims.int_zero)
    | FStar_Reflection_V2_Arith.Mult
        (uu___, FStar_Reflection_V2_Arith.Lit uu___1) when
        uu___1 = Prims.int_zero ->
        (FStar_Tactics_V2_Derived.apply_lemma
           (FStarC_Reflection_V2_Builtins.pack_ln
              (FStarC_Reflection_V2_Data.Tv_FVar
                 (FStarC_Reflection_V2_Builtins.pack_fv
                    ["FStar"; "Tactics"; "Canon"; "Lemmas"; "x_mult_zero"])))
           ps;
         FStar_Reflection_V2_Arith.Lit Prims.int_zero)
    | FStar_Reflection_V2_Arith.Mult (FStar_Reflection_V2_Arith.Lit uu___, r)
        when uu___ = Prims.int_one ->
        (FStar_Tactics_V2_Derived.apply_lemma
           (FStarC_Reflection_V2_Builtins.pack_ln
              (FStarC_Reflection_V2_Data.Tv_FVar
                 (FStarC_Reflection_V2_Builtins.pack_fv
                    ["FStar"; "Tactics"; "Canon"; "Lemmas"; "one_mult_x"])))
           ps;
         r)
    | FStar_Reflection_V2_Arith.Mult (l, FStar_Reflection_V2_Arith.Lit uu___)
        when uu___ = Prims.int_one ->
        (FStar_Tactics_V2_Derived.apply_lemma
           (FStarC_Reflection_V2_Builtins.pack_ln
              (FStarC_Reflection_V2_Data.Tv_FVar
                 (FStarC_Reflection_V2_Builtins.pack_fv
                    ["FStar"; "Tactics"; "Canon"; "Lemmas"; "x_mult_one"])))
           ps;
         l)
    | FStar_Reflection_V2_Arith.Mult (a, b) ->
        if FStar_Order.gt (FStar_Reflection_V2_Arith.compare_expr a b)
        then
          (FStar_Tactics_V2_Derived.apply_lemma
             (FStarC_Reflection_V2_Builtins.pack_ln
                (FStarC_Reflection_V2_Data.Tv_FVar
                   (FStarC_Reflection_V2_Builtins.pack_fv
                      ["FStar"; "Tactics"; "Canon"; "Lemmas"; "comm_mult"])))
             ps;
           FStar_Reflection_V2_Arith.Mult (b, a))
        else x () ps
    | FStar_Reflection_V2_Arith.Minus (a, b) ->
        (step_lemma
           (FStarC_Reflection_V2_Builtins.pack_ln
              (FStarC_Reflection_V2_Data.Tv_FVar
                 (FStarC_Reflection_V2_Builtins.pack_fv
                    ["FStar"; "Tactics"; "Canon"; "Lemmas"; "minus_is_plus"])))
           ps;
         step_lemma
           (FStarC_Reflection_V2_Builtins.pack_ln
              (FStarC_Reflection_V2_Data.Tv_FVar
                 (FStarC_Reflection_V2_Builtins.pack_fv
                    ["FStar"; "Tactics"; "Canon"; "Lemmas"; "cong_plus"])))
           ps;
         FStar_Tactics_V2_Derived.trefl () ps;
         (let x4 =
            match b with
            | FStar_Reflection_V2_Arith.Lit n ->
                FStar_Reflection_V2_Arith.Lit (- n)
            | uu___ -> FStar_Reflection_V2_Arith.Neg b in
          let x5 = canon_point x4 ps in
          canon_point (FStar_Reflection_V2_Arith.Plus (a, x5)) ps))
    | uu___ -> x () ps
let canon_point_entry (uu___ : unit) :
  (unit, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    FStarC_Tactics_V2_Builtins.norm [Fstarcompiler.FStarC_NormSteps.primops]
      ps;
    (let x1 = FStar_Tactics_V2_Derived.cur_goal () ps in
     let x2 = FStar_Reflection_V2_Formula.term_as_formula x1 ps in
     match x2 with
     | FStar_Reflection_V2_Formula.Comp
         (FStar_Reflection_V2_Formula.Eq uu___1, l, r) ->
         let x3 =
           FStar_Reflection_V2_Arith.run_tm
             (FStar_Reflection_V2_Arith.is_arith_expr l) ps in
         (match x3 with
          | Fstarcompiler.FStar_Pervasives.Inr e ->
              let x4 = canon_point e ps in ()
          | Fstarcompiler.FStar_Pervasives.Inl uu___2 ->
              FStar_Tactics_V2_Derived.trefl () ps)
     | uu___1 ->
         let x3 =
           let x4 = FStarC_Tactics_V2_Builtins.term_to_string x1 ps in
           Prims.strcat "impossible: " x4 in
         FStar_Tactics_V2_Derived.fail x3 ps)
let canon (uu___ : unit) : (unit, unit) FStar_Tactics_Effect.tac_repr=
  FStar_Tactics_V2_Derived.pointwise canon_point_entry
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.Canon.canon" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.Canon.canon (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_1 canon)
               Fstarcompiler.FStarC_Syntax_Embeddings.e_unit
               Fstarcompiler.FStarC_Syntax_Embeddings.e_unit psc ncb us args)
