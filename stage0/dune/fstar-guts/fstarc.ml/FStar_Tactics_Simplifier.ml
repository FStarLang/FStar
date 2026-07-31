open Prims
let tiff (uu___ : unit) : (unit, Obj.t) FStar_Tactics_Effect.tac_repr=
  FStar_Tactics_V2_Derived.apply_lemma
    (FStarC_Reflection_V2_Builtins.pack_ln
       (FStarC_Reflection_V2_Data.Tv_FVar
          (FStarC_Reflection_V2_Builtins.pack_fv
             ["FStar"; "Tactics"; "Simplifier"; "lem_iff_refl"])))
let step (uu___ : unit) : (unit, Obj.t) FStar_Tactics_Effect.tac_repr=
  FStar_Tactics_V2_Derived.apply_lemma
    (FStarC_Reflection_V2_Builtins.pack_ln
       (FStarC_Reflection_V2_Data.Tv_FVar
          (FStarC_Reflection_V2_Builtins.pack_fv
             ["FStar"; "Tactics"; "Simplifier"; "lem_iff_trans"])))
let is_true (t : FStar_Tactics_NamedView.term) :
  (Prims.bool, Obj.t) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = FStar_Reflection_V2_Formula.term_as_formula' t ps in
    match x with
    | FStar_Reflection_V2_Formula.True_ -> true
    | uu___ ->
        let x1 = FStar_Tactics_NamedView.inspect t ps in
        (match x1 with
         | FStar_Tactics_NamedView.Tv_App (l, r) ->
             let x2 = FStar_Tactics_NamedView.inspect l ps in
             (match x2 with
              | FStar_Tactics_NamedView.Tv_Abs (b, t1) ->
                  let x3 = FStar_Reflection_V2_Formula.term_as_formula' t1 ps in
                  (match x3 with
                   | FStar_Reflection_V2_Formula.True_ -> true
                   | uu___1 -> false)
              | uu___1 -> false)
         | uu___1 -> false)
let is_false (t : FStar_Tactics_NamedView.term) :
  (Prims.bool, Obj.t) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = FStar_Reflection_V2_Formula.term_as_formula' t ps in
    match x with
    | FStar_Reflection_V2_Formula.False_ -> true
    | uu___ ->
        let x1 = FStar_Tactics_NamedView.inspect t ps in
        (match x1 with
         | FStar_Tactics_NamedView.Tv_App (l, r) ->
             let x2 = FStar_Tactics_NamedView.inspect l ps in
             (match x2 with
              | FStar_Tactics_NamedView.Tv_Abs (b, t1) ->
                  let x3 = FStar_Reflection_V2_Formula.term_as_formula' t1 ps in
                  (match x3 with
                   | FStar_Reflection_V2_Formula.False_ -> true
                   | uu___1 -> false)
              | uu___1 -> false)
         | uu___1 -> false)
let inhabit (uu___ : unit) : (unit, Obj.t) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = FStar_Tactics_V2_Derived.cur_goal () ps in
    let x1 = FStar_Tactics_NamedView.inspect x ps in
    match x1 with
    | FStar_Tactics_NamedView.Tv_FVar fv ->
        let x2 = FStarC_Reflection_V2_Builtins.inspect_fv fv in
        if x2 = FStar_Reflection_Const.int_lid
        then
          FStar_Tactics_V2_Derived.exact
            (FStarC_Reflection_V2_Builtins.pack_ln
               (FStarC_Reflection_V2_Data.Tv_Const
                  (FStarC_Reflection_V2_Data.C_Int (Prims.of_int 42)))) ps
        else
          if x2 = FStar_Reflection_Const.bool_lid
          then
            FStar_Tactics_V2_Derived.exact
              (FStarC_Reflection_V2_Builtins.pack_ln
                 (FStarC_Reflection_V2_Data.Tv_Const
                    FStarC_Reflection_V2_Data.C_True)) ps
          else
            if x2 = FStar_Reflection_Const.unit_lid
            then
              FStar_Tactics_V2_Derived.exact
                (FStarC_Reflection_V2_Builtins.pack_ln
                   (FStarC_Reflection_V2_Data.Tv_Const
                      FStarC_Reflection_V2_Data.C_Unit)) ps
            else FStar_Tactics_V2_Derived.fail "" ps
    | uu___1 -> FStar_Tactics_V2_Derived.fail "" ps
let rec simplify_point (uu___ : unit) :
  (unit, Obj.t) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    recurse () ps;
    FStarC_Tactics_V2_Builtins.norm [] ps;
    (let x2 = FStar_Tactics_V2_Derived.cur_goal () ps in
     let x3 = FStar_Reflection_V2_Formula.term_as_formula x2 ps in
     match x3 with
     | FStar_Reflection_V2_Formula.Iff (l, r) ->
         let x4 = FStar_Reflection_V2_Formula.term_as_formula' l ps in
         (match x4 with
          | FStar_Reflection_V2_Formula.And (p, q) ->
              let x5 = is_true p ps in
              if x5
              then
                FStar_Tactics_V2_Derived.apply_lemma
                  (FStarC_Reflection_V2_Builtins.pack_ln
                     (FStarC_Reflection_V2_Data.Tv_FVar
                        (FStarC_Reflection_V2_Builtins.pack_fv
                           ["FStar";
                           "Tactics";
                           "Simplifier";
                           "lem_true_and_p"]))) ps
              else
                (let x6 = is_true q ps in
                 if x6
                 then
                   FStar_Tactics_V2_Derived.apply_lemma
                     (FStarC_Reflection_V2_Builtins.pack_ln
                        (FStarC_Reflection_V2_Data.Tv_FVar
                           (FStarC_Reflection_V2_Builtins.pack_fv
                              ["FStar";
                              "Tactics";
                              "Simplifier";
                              "lem_p_and_true"]))) ps
                 else
                   (let x7 = is_false p ps in
                    if x7
                    then
                      FStar_Tactics_V2_Derived.apply_lemma
                        (FStarC_Reflection_V2_Builtins.pack_ln
                           (FStarC_Reflection_V2_Data.Tv_FVar
                              (FStarC_Reflection_V2_Builtins.pack_fv
                                 ["FStar";
                                 "Tactics";
                                 "Simplifier";
                                 "lem_false_and_p"]))) ps
                    else
                      (let x8 = is_false q ps in
                       if x8
                       then
                         FStar_Tactics_V2_Derived.apply_lemma
                           (FStarC_Reflection_V2_Builtins.pack_ln
                              (FStarC_Reflection_V2_Data.Tv_FVar
                                 (FStarC_Reflection_V2_Builtins.pack_fv
                                    ["FStar";
                                    "Tactics";
                                    "Simplifier";
                                    "lem_p_and_false"]))) ps
                       else tiff () ps)))
          | FStar_Reflection_V2_Formula.Or (p, q) ->
              let x5 = is_true p ps in
              if x5
              then
                FStar_Tactics_V2_Derived.apply_lemma
                  (FStarC_Reflection_V2_Builtins.pack_ln
                     (FStarC_Reflection_V2_Data.Tv_FVar
                        (FStarC_Reflection_V2_Builtins.pack_fv
                           ["FStar";
                           "Tactics";
                           "Simplifier";
                           "lem_true_or_p"]))) ps
              else
                (let x6 = is_true q ps in
                 if x6
                 then
                   FStar_Tactics_V2_Derived.apply_lemma
                     (FStarC_Reflection_V2_Builtins.pack_ln
                        (FStarC_Reflection_V2_Data.Tv_FVar
                           (FStarC_Reflection_V2_Builtins.pack_fv
                              ["FStar";
                              "Tactics";
                              "Simplifier";
                              "lem_p_or_true"]))) ps
                 else
                   (let x7 = is_false p ps in
                    if x7
                    then
                      FStar_Tactics_V2_Derived.apply_lemma
                        (FStarC_Reflection_V2_Builtins.pack_ln
                           (FStarC_Reflection_V2_Data.Tv_FVar
                              (FStarC_Reflection_V2_Builtins.pack_fv
                                 ["FStar";
                                 "Tactics";
                                 "Simplifier";
                                 "lem_false_or_p"]))) ps
                    else
                      (let x8 = is_false q ps in
                       if x8
                       then
                         FStar_Tactics_V2_Derived.apply_lemma
                           (FStarC_Reflection_V2_Builtins.pack_ln
                              (FStarC_Reflection_V2_Data.Tv_FVar
                                 (FStarC_Reflection_V2_Builtins.pack_fv
                                    ["FStar";
                                    "Tactics";
                                    "Simplifier";
                                    "lem_p_or_false"]))) ps
                       else tiff () ps)))
          | FStar_Reflection_V2_Formula.Implies (p, q) ->
              let x5 = is_true p ps in
              if x5
              then
                FStar_Tactics_V2_Derived.apply_lemma
                  (FStarC_Reflection_V2_Builtins.pack_ln
                     (FStarC_Reflection_V2_Data.Tv_FVar
                        (FStarC_Reflection_V2_Builtins.pack_fv
                           ["FStar";
                           "Tactics";
                           "Simplifier";
                           "lem_true_imp_p"]))) ps
              else
                (let x6 = is_true q ps in
                 if x6
                 then
                   FStar_Tactics_V2_Derived.apply_lemma
                     (FStarC_Reflection_V2_Builtins.pack_ln
                        (FStarC_Reflection_V2_Data.Tv_FVar
                           (FStarC_Reflection_V2_Builtins.pack_fv
                              ["FStar";
                              "Tactics";
                              "Simplifier";
                              "lem_p_imp_true"]))) ps
                 else
                   (let x7 = is_false p ps in
                    if x7
                    then
                      FStar_Tactics_V2_Derived.apply_lemma
                        (FStarC_Reflection_V2_Builtins.pack_ln
                           (FStarC_Reflection_V2_Data.Tv_FVar
                              (FStarC_Reflection_V2_Builtins.pack_fv
                                 ["FStar";
                                 "Tactics";
                                 "Simplifier";
                                 "lem_false_imp_p"]))) ps
                    else tiff () ps))
          | FStar_Reflection_V2_Formula.Forall (_b, _sort, p) ->
              let x5 = is_true p ps in
              if x5
              then
                FStar_Tactics_V2_Derived.apply_lemma
                  (FStarC_Reflection_V2_Builtins.pack_ln
                     (FStarC_Reflection_V2_Data.Tv_FVar
                        (FStarC_Reflection_V2_Builtins.pack_fv
                           ["FStar"; "Tactics"; "Simplifier"; "lem_fa_true"])))
                  ps
              else
                (let x6 = is_false p ps in
                 if x6
                 then
                   FStar_Tactics_V2_Derived.or_else
                     (fun uu___1 ps1 ->
                        FStar_Tactics_V2_Derived.apply_lemma
                          (FStarC_Reflection_V2_Builtins.pack_ln
                             (FStarC_Reflection_V2_Data.Tv_FVar
                                (FStarC_Reflection_V2_Builtins.pack_fv
                                   ["FStar";
                                   "Tactics";
                                   "Simplifier";
                                   "lem_fa_false"]))) ps1;
                        inhabit () ps1) tiff ps
                 else tiff () ps)
          | FStar_Reflection_V2_Formula.Exists (_b, _sort, p) ->
              let x5 = is_false p ps in
              if x5
              then
                FStar_Tactics_V2_Derived.apply_lemma
                  (FStarC_Reflection_V2_Builtins.pack_ln
                     (FStarC_Reflection_V2_Data.Tv_FVar
                        (FStarC_Reflection_V2_Builtins.pack_fv
                           ["FStar"; "Tactics"; "Simplifier"; "lem_ex_false"])))
                  ps
              else
                (let x6 = is_true p ps in
                 if x6
                 then
                   FStar_Tactics_V2_Derived.or_else
                     (fun uu___1 ps1 ->
                        FStar_Tactics_V2_Derived.apply_lemma
                          (FStarC_Reflection_V2_Builtins.pack_ln
                             (FStarC_Reflection_V2_Data.Tv_FVar
                                (FStarC_Reflection_V2_Builtins.pack_fv
                                   ["FStar";
                                   "Tactics";
                                   "Simplifier";
                                   "lem_ex_true"]))) ps1;
                        inhabit () ps1) tiff ps
                 else tiff () ps)
          | FStar_Reflection_V2_Formula.Not p ->
              let x5 = is_true p ps in
              if x5
              then
                FStar_Tactics_V2_Derived.apply_lemma
                  (FStarC_Reflection_V2_Builtins.pack_ln
                     (FStarC_Reflection_V2_Data.Tv_FVar
                        (FStarC_Reflection_V2_Builtins.pack_fv
                           ["FStar"; "Tactics"; "Simplifier"; "lem_neg_true"])))
                  ps
              else
                (let x6 = is_false p ps in
                 if x6
                 then
                   FStar_Tactics_V2_Derived.apply_lemma
                     (FStarC_Reflection_V2_Builtins.pack_ln
                        (FStarC_Reflection_V2_Data.Tv_FVar
                           (FStarC_Reflection_V2_Builtins.pack_fv
                              ["FStar";
                              "Tactics";
                              "Simplifier";
                              "lem_neg_false"]))) ps
                 else tiff () ps)
          | FStar_Reflection_V2_Formula.Iff (p, q) ->
              (step () ps;
               (let x7 = is_true p ps in
                if x7
                then
                  FStar_Tactics_V2_Derived.apply_lemma
                    (FStarC_Reflection_V2_Builtins.pack_ln
                       (FStarC_Reflection_V2_Data.Tv_FVar
                          (FStarC_Reflection_V2_Builtins.pack_fv
                             ["FStar";
                             "Tactics";
                             "Simplifier";
                             "lem_true_iff_p"]))) ps
                else
                  (let x8 = is_true q ps in
                   if x8
                   then
                     FStar_Tactics_V2_Derived.apply_lemma
                       (FStarC_Reflection_V2_Builtins.pack_ln
                          (FStarC_Reflection_V2_Data.Tv_FVar
                             (FStarC_Reflection_V2_Builtins.pack_fv
                                ["FStar";
                                "Tactics";
                                "Simplifier";
                                "lem_p_iff_true"]))) ps
                   else
                     (let x9 = is_false p ps in
                      if x9
                      then
                        FStar_Tactics_V2_Derived.apply_lemma
                          (FStarC_Reflection_V2_Builtins.pack_ln
                             (FStarC_Reflection_V2_Data.Tv_FVar
                                (FStarC_Reflection_V2_Builtins.pack_fv
                                   ["FStar";
                                   "Tactics";
                                   "Simplifier";
                                   "lem_false_iff_p"]))) ps
                      else
                        (let x10 = is_false q ps in
                         if x10
                         then
                           FStar_Tactics_V2_Derived.apply_lemma
                             (FStarC_Reflection_V2_Builtins.pack_ln
                                (FStarC_Reflection_V2_Data.Tv_FVar
                                   (FStarC_Reflection_V2_Builtins.pack_fv
                                      ["FStar";
                                      "Tactics";
                                      "Simplifier";
                                      "lem_p_iff_false"]))) ps
                         else tiff () ps))));
               simplify_point () ps)
          | uu___1 -> tiff () ps)
     | uu___1 ->
         FStar_Tactics_V2_Derived.fail
           "simplify_point: failed precondition: goal should be `g <==> ?u`"
           ps)
and recurse (uu___ : unit) : (unit, Obj.t) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    step () ps;
    FStarC_Tactics_V2_Builtins.norm [] ps;
    (let x2 = FStar_Tactics_V2_Derived.cur_goal () ps in
     let x3 = FStar_Reflection_V2_Formula.term_as_formula x2 ps in
     match x3 with
     | FStar_Reflection_V2_Formula.Iff (l, r) ->
         let x4 = FStar_Reflection_V2_Formula.term_as_formula' l ps in
         (match x4 with
          | FStar_Reflection_V2_Formula.And (uu___1, uu___2) ->
              FStar_Tactics_V2_Derived.seq
                (fun uu___3 ->
                   FStar_Tactics_V2_Derived.apply_lemma
                     (FStarC_Reflection_V2_Builtins.pack_ln
                        (FStarC_Reflection_V2_Data.Tv_FVar
                           (FStarC_Reflection_V2_Builtins.pack_fv
                              ["FStar"; "Tactics"; "Simplifier"; "and_cong"]))))
                simplify_point ps
          | FStar_Reflection_V2_Formula.Or (uu___1, uu___2) ->
              FStar_Tactics_V2_Derived.seq
                (fun uu___3 ->
                   FStar_Tactics_V2_Derived.apply_lemma
                     (FStarC_Reflection_V2_Builtins.pack_ln
                        (FStarC_Reflection_V2_Data.Tv_FVar
                           (FStarC_Reflection_V2_Builtins.pack_fv
                              ["FStar"; "Tactics"; "Simplifier"; "or_cong"]))))
                simplify_point ps
          | FStar_Reflection_V2_Formula.Implies (uu___1, uu___2) ->
              FStar_Tactics_V2_Derived.seq
                (fun uu___3 ->
                   FStar_Tactics_V2_Derived.apply_lemma
                     (FStarC_Reflection_V2_Builtins.pack_ln
                        (FStarC_Reflection_V2_Data.Tv_FVar
                           (FStarC_Reflection_V2_Builtins.pack_fv
                              ["FStar"; "Tactics"; "Simplifier"; "imp_cong"]))))
                simplify_point ps
          | FStar_Reflection_V2_Formula.Forall (uu___1, uu___2, uu___3) ->
              (FStar_Tactics_V2_Derived.apply_lemma
                 (FStarC_Reflection_V2_Builtins.pack_ln
                    (FStarC_Reflection_V2_Data.Tv_FVar
                       (FStarC_Reflection_V2_Builtins.pack_fv
                          ["FStar"; "Tactics"; "Simplifier"; "fa_cong"]))) ps;
               (let x6 = FStarC_Tactics_V2_Builtins.intro () ps in
                simplify_point () ps))
          | FStar_Reflection_V2_Formula.Exists (uu___1, uu___2, uu___3) ->
              (FStar_Tactics_V2_Derived.apply_lemma
                 (FStarC_Reflection_V2_Builtins.pack_ln
                    (FStarC_Reflection_V2_Data.Tv_FVar
                       (FStarC_Reflection_V2_Builtins.pack_fv
                          ["FStar"; "Tactics"; "Simplifier"; "ex_cong"]))) ps;
               (let x6 = FStarC_Tactics_V2_Builtins.intro () ps in
                simplify_point () ps))
          | FStar_Reflection_V2_Formula.Not uu___1 ->
              (FStar_Tactics_V2_Derived.apply_lemma
                 (FStarC_Reflection_V2_Builtins.pack_ln
                    (FStarC_Reflection_V2_Data.Tv_FVar
                       (FStarC_Reflection_V2_Builtins.pack_fv
                          ["FStar"; "Tactics"; "Simplifier"; "neg_cong"])))
                 ps;
               simplify_point () ps)
          | FStar_Reflection_V2_Formula.Iff (uu___1, uu___2) ->
              FStar_Tactics_V2_Derived.seq
                (fun uu___3 ->
                   FStar_Tactics_V2_Derived.apply_lemma
                     (FStarC_Reflection_V2_Builtins.pack_ln
                        (FStarC_Reflection_V2_Data.Tv_FVar
                           (FStarC_Reflection_V2_Builtins.pack_fv
                              ["FStar"; "Tactics"; "Simplifier"; "iff_cong"]))))
                simplify_point ps
          | uu___1 -> tiff () ps)
     | uu___1 ->
         FStar_Tactics_V2_Derived.fail
           "recurse: failed precondition: goal should be `g <==> ?u`" ps)
let simplify (uu___ : unit) : (unit, Obj.t) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    FStar_Tactics_V2_Derived.apply_lemma
      (FStarC_Reflection_V2_Builtins.pack_ln
         (FStarC_Reflection_V2_Data.Tv_FVar
            (FStarC_Reflection_V2_Builtins.pack_fv
               ["FStar"; "Tactics"; "Simplifier"; "equiv"]))) ps;
    simplify_point () ps
