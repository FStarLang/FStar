open Prims
let term_eq :
  FStarC_Reflection_Types.term -> FStarC_Reflection_Types.term -> Prims.bool=
  FStar_Reflection_TermEq_Simple.term_eq
let dump (m : Prims.string) : (unit, Obj.t) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x = FStarC_Tactics_V2_Builtins.debugging () ps in
    if x then FStarC_Tactics_V2_Builtins.dump m ps else ()
type 'a exp =
  | Unit 
  | Var of 'a 
  | Mult of 'a exp * 'a exp 
let uu___is_Unit (projectee : 'a exp) : Prims.bool=
  match projectee with | Unit -> true | uu___ -> false
let uu___is_Var (projectee : 'a exp) : Prims.bool=
  match projectee with | Var _0 -> true | uu___ -> false
let __proj__Var__item___0 (projectee : 'a exp) : 'a=
  match projectee with | Var _0 -> _0
let uu___is_Mult (projectee : 'a exp) : Prims.bool=
  match projectee with | Mult (_0, _1) -> true | uu___ -> false
let __proj__Mult__item___0 (projectee : 'a exp) : 'a exp=
  match projectee with | Mult (_0, _1) -> _0
let __proj__Mult__item___1 (projectee : 'a exp) : 'a exp=
  match projectee with | Mult (_0, _1) -> _1
let rec exp_to_string : 'a . ('a -> Prims.string) -> 'a exp -> Prims.string =
  fun a_to_string e ->
    match e with
    | Unit -> "Unit"
    | Var x -> Prims.strcat "Var " (a_to_string x)
    | Mult (e1, e2) ->
        Prims.strcat "Mult ("
          (Prims.strcat (exp_to_string a_to_string e1)
             (Prims.strcat ") ("
                (Prims.strcat (exp_to_string a_to_string e2) ")")))
let rec mdenote : 'a . 'a FStar_Algebra_Monoid.monoid -> 'a exp -> 'a =
  fun m e ->
    match e with
    | Unit -> FStar_Algebra_Monoid.__proj__Monoid__item__unit m
    | Var x -> x
    | Mult (e1, e2) ->
        FStar_Algebra_Monoid.__proj__Monoid__item__mult m (mdenote m e1)
          (mdenote m e2)
let rec mldenote : 'a . 'a FStar_Algebra_Monoid.monoid -> 'a Prims.list -> 'a
  =
  fun m xs ->
    match xs with
    | [] -> FStar_Algebra_Monoid.__proj__Monoid__item__unit m
    | x::[] -> x
    | x::xs' ->
        FStar_Algebra_Monoid.__proj__Monoid__item__mult m x (mldenote m xs')
let rec flatten : 'a . 'a exp -> 'a Prims.list =
  fun e ->
    match e with
    | Unit -> []
    | Var x -> [x]
    | Mult (e1, e2) -> FStar_List_Tot_Base.op_At (flatten e1) (flatten e2)
let rec reification_aux :
  'a .
    FStar_Tactics_NamedView.term ->
      FStar_Tactics_NamedView.term ->
        FStar_Tactics_NamedView.term ->
          ('a exp, Obj.t) FStar_Tactics_Effect.tac_repr
  =
  fun mult unit me ps ->
    let x = FStar_Reflection_V2_Derived_Lemmas.collect_app_ref me in
    match x with
    | (hd, tl) ->
        let x1 = FStar_List_Tot_Base.list_unref () tl in
        let x2 = let x3 = FStar_Tactics_NamedView.inspect hd ps in (x3, x1) in
        (match x2 with
         | (FStar_Tactics_NamedView.Tv_FVar fv,
            (me1, FStarC_Reflection_V2_Data.Q_Explicit)::(me2,
                                                          FStarC_Reflection_V2_Data.Q_Explicit)::[])
             ->
             if
               term_eq
                 (FStar_Tactics_NamedView.pack
                    (FStar_Tactics_NamedView.Tv_FVar fv)) mult
             then
               let x3 = reification_aux mult unit me1 ps in
               let x4 = reification_aux mult unit me2 ps in Mult (x3, x4)
             else
               (let x3 = FStarC_Tactics_V2_Builtins.unquote me ps in Var x3)
         | (uu___, uu___1) ->
             if term_eq me unit
             then Unit
             else
               (let x3 = FStarC_Tactics_V2_Builtins.unquote me ps in Var x3))
let reification (m : 'a FStar_Algebra_Monoid.monoid)
  (me : FStar_Tactics_NamedView.term) :
  ('a exp, Obj.t) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x =
      let x1 =
        Obj.magic (failwith "Cannot evaluate open quotation at runtime") in
      FStar_Tactics_V2_Derived.norm_term
        [FStarC_NormSteps.delta;
        FStarC_NormSteps.zeta;
        FStarC_NormSteps.iota] x1 ps in
    let x1 =
      let x2 =
        Obj.magic (failwith "Cannot evaluate open quotation at runtime") in
      FStar_Tactics_V2_Derived.norm_term
        [FStarC_NormSteps.delta;
        FStarC_NormSteps.zeta;
        FStarC_NormSteps.iota] x2 ps in
    let x2 =
      FStar_Tactics_V2_Derived.norm_term
        [FStarC_NormSteps.delta;
        FStarC_NormSteps.zeta;
        FStarC_NormSteps.iota] me ps in
    reification_aux x x1 x2 ps
let canon_monoid (m : 'a FStar_Algebra_Monoid.monoid) :
  (unit, Obj.t) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    FStarC_Tactics_V2_Builtins.norm [] ps;
    (let x1 = FStar_Tactics_V2_Derived.cur_goal () ps in
     let x2 = FStar_Reflection_V2_Formula.term_as_formula x1 ps in
     match x2 with
     | FStar_Reflection_V2_Formula.Comp
         (FStar_Reflection_V2_Formula.Eq (FStar_Pervasives_Native.Some t),
          me1, me2)
         ->
         let x3 =
           let x4 =
             let x5 = me2 in
             let x6 = me1 in
             let x7 =
               Obj.magic
                 (failwith "Cannot evaluate open quotation at runtime") in
             FStarC_Reflection_V2_Builtins.pack_ln
               (FStarC_Reflection_V2_Data.Tv_App
                  ((FStarC_Reflection_V2_Builtins.pack_ln
                      (FStarC_Reflection_V2_Data.Tv_FVar
                         (FStarC_Reflection_V2_Builtins.pack_fv
                            ["Prims"; "squash"]))),
                    ((FStarC_Reflection_V2_Builtins.pack_ln
                        (FStarC_Reflection_V2_Data.Tv_App
                           ((FStarC_Reflection_V2_Builtins.pack_ln
                               (FStarC_Reflection_V2_Data.Tv_App
                                  ((FStarC_Reflection_V2_Builtins.pack_ln
                                      (FStarC_Reflection_V2_Data.Tv_App
                                         ((FStarC_Reflection_V2_Builtins.pack_ln
                                             (FStarC_Reflection_V2_Data.Tv_FVar
                                                (FStarC_Reflection_V2_Builtins.pack_fv
                                                   ["Prims"; "eq2"]))),
                                           (x7,
                                             FStarC_Reflection_V2_Data.Q_Implicit)))),
                                    (x6,
                                      FStarC_Reflection_V2_Data.Q_Explicit)))),
                             (x5, FStarC_Reflection_V2_Data.Q_Explicit)))),
                      FStarC_Reflection_V2_Data.Q_Explicit))) in
           FStar_Tactics_V2_Derived.tcut x4 ps in
         (FStar_Tactics_V2_Derived.smt () ps;
          (let x5 = reification m me1 ps in
           let x6 = reification m me2 ps in
           (let x8 =
              Obj.magic
                (failwith "Cannot evaluate open quotation at runtime") in
            FStar_Tactics_V2_Derived.change_sq x8 ps);
           FStar_Tactics_V2_Derived.apply
             (FStarC_Reflection_V2_Builtins.pack_ln
                (FStarC_Reflection_V2_Data.Tv_FVar
                   (FStarC_Reflection_V2_Builtins.pack_fv
                      ["FStar"; "Tactics"; "CanonMonoid"; "monoid_reflect"])))
             ps;
           FStarC_Tactics_V2_Builtins.norm
             [FStarC_NormSteps.delta_only
                ["FStar.Tactics.CanonMonoid.mldenote";
                "FStar.Tactics.CanonMonoid.flatten";
                "FStar.List.Tot.Base.op_At";
                "FStar.List.Tot.Base.append"]] ps))
     | uu___ -> FStar_Tactics_V2_Derived.fail "Goal should be an equality" ps)
