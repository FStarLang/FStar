open Prims
let (term_eq :
  FStarC_Reflection_Types.term -> FStarC_Reflection_Types.term -> Prims.bool)
  = FStar_Reflection_TermEq_Simple.term_eq
let (dump : Prims.string -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun m ->
    let uu___ = FStarC_Tactics_V2_Builtins.debugging () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.CanonMonoid.fst"
               (Prims.of_int (27)) (Prims.of_int (16)) (Prims.of_int (27))
               (Prims.of_int (28)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.CanonMonoid.fst"
               (Prims.of_int (27)) (Prims.of_int (13)) (Prims.of_int (27))
               (Prims.of_int (40))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun uu___1 ->
            if uu___1
            then Obj.magic (Obj.repr (FStarC_Tactics_V2_Builtins.dump m))
            else
              Obj.magic
                (Obj.repr
                   (FStar_Tactics_Effect.lift_div_tac (fun uu___3 -> ()))))
           uu___1)
type 'a exp =
  | Unit 
  | Var of 'a 
  | Mult of 'a exp * 'a exp 
let uu___is_Unit : 'a . 'a exp -> Prims.bool =
  fun projectee -> match projectee with | Unit -> true | uu___ -> false
let uu___is_Var : 'a . 'a exp -> Prims.bool =
  fun projectee -> match projectee with | Var _0 -> true | uu___ -> false
let __proj__Var__item___0 : 'a . 'a exp -> 'a =
  fun projectee -> match projectee with | Var _0 -> _0
let uu___is_Mult : 'a . 'a exp -> Prims.bool =
  fun projectee ->
    match projectee with | Mult (_0, _1) -> true | uu___ -> false
let __proj__Mult__item___0 : 'a . 'a exp -> 'a exp =
  fun projectee -> match projectee with | Mult (_0, _1) -> _0
let __proj__Mult__item___1 : 'a . 'a exp -> 'a exp =
  fun projectee -> match projectee with | Mult (_0, _1) -> _1
let rec exp_to_string : 'a . ('a -> Prims.string) -> 'a exp -> Prims.string =
  fun a_to_string ->
    fun e ->
      match e with
      | Unit -> "Unit"
      | Var x -> Prims.strcat "Var " (a_to_string x)
      | Mult (e1, e2) ->
          Prims.strcat "Mult ("
            (Prims.strcat (exp_to_string a_to_string e1)
               (Prims.strcat ") ("
                  (Prims.strcat (exp_to_string a_to_string e2) ")")))
let rec mdenote : 'a . 'a FStar_Algebra_Monoid.monoid -> 'a exp -> 'a =
  fun m ->
    fun e ->
      match e with
      | Unit -> FStar_Algebra_Monoid.__proj__Monoid__item__unit m
      | Var x -> x
      | Mult (e1, e2) ->
          FStar_Algebra_Monoid.__proj__Monoid__item__mult m (mdenote m e1)
            (mdenote m e2)
let rec mldenote : 'a . 'a FStar_Algebra_Monoid.monoid -> 'a Prims.list -> 'a
  =
  fun m ->
    fun xs ->
      match xs with
      | [] -> FStar_Algebra_Monoid.__proj__Monoid__item__unit m
      | x::[] -> x
      | x::xs' ->
          FStar_Algebra_Monoid.__proj__Monoid__item__mult m x
            (mldenote m xs')
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
          ('a exp, unit) FStar_Tactics_Effect.tac_repr
  =
  fun mult ->
    fun unit ->
      fun me ->
        let uu___ =
          Obj.magic
            (FStar_Tactics_Effect.lift_div_tac
               (fun uu___1 ->
                  FStar_Reflection_V2_Derived_Lemmas.collect_app_ref me)) in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.CanonMonoid.fst"
                   (Prims.of_int (87)) (Prims.of_int (15))
                   (Prims.of_int (87)) (Prims.of_int (33)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.CanonMonoid.fst"
                   (Prims.of_int (86)) (Prims.of_int (71))
                   (Prims.of_int (97)) (Prims.of_int (25)))))
          (Obj.magic uu___)
          (fun uu___1 ->
             (fun uu___1 ->
                match uu___1 with
                | (hd, tl) ->
                    let uu___2 =
                      Obj.magic
                        (FStar_Tactics_Effect.lift_div_tac
                           (fun uu___3 -> FStar_List_Tot_Base.list_unref tl)) in
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.Tactics.CanonMonoid.fst"
                                  (Prims.of_int (88)) (Prims.of_int (11))
                                  (Prims.of_int (88)) (Prims.of_int (24)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.Tactics.CanonMonoid.fst"
                                  (Prims.of_int (89)) (Prims.of_int (2))
                                  (Prims.of_int (97)) (Prims.of_int (25)))))
                         (Obj.magic uu___2)
                         (fun uu___3 ->
                            (fun tl1 ->
                               let uu___3 =
                                 let uu___4 =
                                   FStar_Tactics_NamedView.inspect hd in
                                 FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "FStar.Tactics.CanonMonoid.fst"
                                            (Prims.of_int (89))
                                            (Prims.of_int (8))
                                            (Prims.of_int (89))
                                            (Prims.of_int (18)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "FStar.Tactics.CanonMonoid.fst"
                                            (Prims.of_int (89))
                                            (Prims.of_int (8))
                                            (Prims.of_int (89))
                                            (Prims.of_int (22)))))
                                   (Obj.magic uu___4)
                                   (fun uu___5 ->
                                      FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___6 -> (uu___5, tl1))) in
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.Tactics.CanonMonoid.fst"
                                             (Prims.of_int (89))
                                             (Prims.of_int (8))
                                             (Prims.of_int (89))
                                             (Prims.of_int (22)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.Tactics.CanonMonoid.fst"
                                             (Prims.of_int (89))
                                             (Prims.of_int (2))
                                             (Prims.of_int (97))
                                             (Prims.of_int (25)))))
                                    (Obj.magic uu___3)
                                    (fun uu___4 ->
                                       (fun uu___4 ->
                                          match uu___4 with
                                          | (FStar_Tactics_NamedView.Tv_FVar
                                             fv,
                                             (me1,
                                              FStarC_Reflection_V2_Data.Q_Explicit)::
                                             (me2,
                                              FStarC_Reflection_V2_Data.Q_Explicit)::[])
                                              ->
                                              let uu___5 =
                                                FStarC_Tactics_V2_Builtins.term_eq_old
                                                  (FStar_Tactics_NamedView.pack
                                                     (FStar_Tactics_NamedView.Tv_FVar
                                                        fv)) mult in
                                              Obj.magic
                                                (FStar_Tactics_Effect.tac_bind
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "FStar.Tactics.CanonMonoid.fst"
                                                            (Prims.of_int (91))
                                                            (Prims.of_int (7))
                                                            (Prims.of_int (91))
                                                            (Prims.of_int (43)))))
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "FStar.Tactics.CanonMonoid.fst"
                                                            (Prims.of_int (91))
                                                            (Prims.of_int (4))
                                                            (Prims.of_int (93))
                                                            (Prims.of_int (25)))))
                                                   (Obj.magic uu___5)
                                                   (fun uu___6 ->
                                                      (fun uu___6 ->
                                                         if uu___6
                                                         then
                                                           let uu___7 =
                                                             reification_aux
                                                               mult unit me1 in
                                                           Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonMonoid.fst"
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (45)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonMonoid.fst"
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (77)))))
                                                                (Obj.magic
                                                                   uu___7)
                                                                (fun uu___8
                                                                   ->
                                                                   (fun
                                                                    uu___8 ->
                                                                    let uu___9
                                                                    =
                                                                    reification_aux
                                                                    mult unit
                                                                    me2 in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonMonoid.fst"
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (77)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonMonoid.fst"
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (77)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    Mult
                                                                    (uu___8,
                                                                    uu___10)))))
                                                                    uu___8))
                                                         else
                                                           (let uu___8 =
                                                              FStarC_Tactics_V2_Builtins.unquote
                                                                me in
                                                            Obj.magic
                                                              (FStar_Tactics_Effect.tac_bind
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonMonoid.fst"
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (25)))))
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonMonoid.fst"
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (25)))))
                                                                 (Obj.magic
                                                                    uu___8)
                                                                 (fun uu___9
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    Var
                                                                    uu___9)))))
                                                        uu___6))
                                          | (uu___5, uu___6) ->
                                              let uu___7 =
                                                FStarC_Tactics_V2_Builtins.term_eq_old
                                                  me unit in
                                              Obj.magic
                                                (FStar_Tactics_Effect.tac_bind
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "FStar.Tactics.CanonMonoid.fst"
                                                            (Prims.of_int (95))
                                                            (Prims.of_int (7))
                                                            (Prims.of_int (95))
                                                            (Prims.of_int (26)))))
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "FStar.Tactics.CanonMonoid.fst"
                                                            (Prims.of_int (95))
                                                            (Prims.of_int (4))
                                                            (Prims.of_int (97))
                                                            (Prims.of_int (25)))))
                                                   (Obj.magic uu___7)
                                                   (fun uu___8 ->
                                                      (fun uu___8 ->
                                                         if uu___8
                                                         then
                                                           Obj.magic
                                                             (Obj.repr
                                                                (FStar_Tactics_Effect.lift_div_tac
                                                                   (fun
                                                                    uu___9 ->
                                                                    Unit)))
                                                         else
                                                           Obj.magic
                                                             (Obj.repr
                                                                (let uu___10
                                                                   =
                                                                   FStarC_Tactics_V2_Builtins.unquote
                                                                    me in
                                                                 FStar_Tactics_Effect.tac_bind
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonMonoid.fst"
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (25)))))
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonMonoid.fst"
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (97))
                                                                    (Prims.of_int (25)))))
                                                                   (Obj.magic
                                                                    uu___10)
                                                                   (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    Var
                                                                    uu___11)))))
                                                        uu___8))) uu___4)))
                              uu___3))) uu___1)
let reification :
  'a .
    'a FStar_Algebra_Monoid.monoid ->
      FStar_Tactics_NamedView.term ->
        ('a exp, unit) FStar_Tactics_Effect.tac_repr
  =
  fun m ->
    fun me ->
      let uu___ =
        let uu___1 =
          Obj.magic
            (FStar_Tactics_Effect.lift_div_tac
               (fun uu___2 ->
                  (fun uu___2 ->
                     Obj.magic
                       (failwith "Cannot evaluate open quotation at runtime"))
                    uu___2)) in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.CanonMonoid.fst"
                   (Prims.of_int (100)) (Prims.of_int (43))
                   (Prims.of_int (100)) (Prims.of_int (67)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.CanonMonoid.fst"
                   (Prims.of_int (100)) (Prims.of_int (15))
                   (Prims.of_int (100)) (Prims.of_int (67)))))
          (Obj.magic uu___1)
          (fun uu___2 ->
             (fun uu___2 ->
                Obj.magic
                  (FStar_Tactics_V2_Derived.norm_term
                     [FStar_Pervasives.delta;
                     FStar_Pervasives.zeta;
                     FStar_Pervasives.iota] uu___2)) uu___2) in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.CanonMonoid.fst"
                 (Prims.of_int (100)) (Prims.of_int (15))
                 (Prims.of_int (100)) (Prims.of_int (67)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.CanonMonoid.fst"
                 (Prims.of_int (100)) (Prims.of_int (70))
                 (Prims.of_int (106)) (Prims.of_int (32)))))
        (Obj.magic uu___)
        (fun uu___1 ->
           (fun mult ->
              let uu___1 =
                let uu___2 =
                  Obj.magic
                    (FStar_Tactics_Effect.lift_div_tac
                       (fun uu___3 ->
                          (fun uu___3 ->
                             Obj.magic
                               (failwith
                                  "Cannot evaluate open quotation at runtime"))
                            uu___3)) in
                FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "FStar.Tactics.CanonMonoid.fst"
                           (Prims.of_int (101)) (Prims.of_int (43))
                           (Prims.of_int (101)) (Prims.of_int (67)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "FStar.Tactics.CanonMonoid.fst"
                           (Prims.of_int (101)) (Prims.of_int (15))
                           (Prims.of_int (101)) (Prims.of_int (67)))))
                  (Obj.magic uu___2)
                  (fun uu___3 ->
                     (fun uu___3 ->
                        Obj.magic
                          (FStar_Tactics_V2_Derived.norm_term
                             [FStar_Pervasives.delta;
                             FStar_Pervasives.zeta;
                             FStar_Pervasives.iota] uu___3)) uu___3) in
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.Tactics.CanonMonoid.fst"
                            (Prims.of_int (101)) (Prims.of_int (15))
                            (Prims.of_int (101)) (Prims.of_int (67)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.Tactics.CanonMonoid.fst"
                            (Prims.of_int (101)) (Prims.of_int (70))
                            (Prims.of_int (106)) (Prims.of_int (32)))))
                   (Obj.magic uu___1)
                   (fun uu___2 ->
                      (fun unit ->
                         let uu___2 =
                           FStar_Tactics_V2_Derived.norm_term
                             [FStar_Pervasives.delta;
                             FStar_Pervasives.zeta;
                             FStar_Pervasives.iota] me in
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "FStar.Tactics.CanonMonoid.fst"
                                       (Prims.of_int (102))
                                       (Prims.of_int (15))
                                       (Prims.of_int (102))
                                       (Prims.of_int (45)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "FStar.Tactics.CanonMonoid.fst"
                                       (Prims.of_int (106))
                                       (Prims.of_int (4))
                                       (Prims.of_int (106))
                                       (Prims.of_int (32)))))
                              (Obj.magic uu___2)
                              (fun uu___3 ->
                                 (fun me1 ->
                                    Obj.magic (reification_aux mult unit me1))
                                   uu___3))) uu___2))) uu___1)
let canon_monoid :
  'a .
    'a FStar_Algebra_Monoid.monoid ->
      (unit, unit) FStar_Tactics_Effect.tac_repr
  =
  fun m ->
    let uu___ = FStarC_Tactics_V2_Builtins.norm [] in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.CanonMonoid.fst"
               (Prims.of_int (109)) (Prims.of_int (2)) (Prims.of_int (109))
               (Prims.of_int (9)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.CanonMonoid.fst"
               (Prims.of_int (109)) (Prims.of_int (10)) (Prims.of_int (127))
               (Prims.of_int (42))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun uu___1 ->
            let uu___2 = FStar_Tactics_V2_Derived.cur_goal () in
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.CanonMonoid.fst"
                          (Prims.of_int (110)) (Prims.of_int (10))
                          (Prims.of_int (110)) (Prims.of_int (21)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.CanonMonoid.fst"
                          (Prims.of_int (111)) (Prims.of_int (2))
                          (Prims.of_int (127)) (Prims.of_int (42)))))
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
                                     "FStar.Tactics.CanonMonoid.fst"
                                     (Prims.of_int (111)) (Prims.of_int (8))
                                     (Prims.of_int (111)) (Prims.of_int (25)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.CanonMonoid.fst"
                                     (Prims.of_int (111)) (Prims.of_int (2))
                                     (Prims.of_int (127)) (Prims.of_int (42)))))
                            (Obj.magic uu___3)
                            (fun uu___4 ->
                               (fun uu___4 ->
                                  match uu___4 with
                                  | FStar_Reflection_V2_Formula.Comp
                                      (FStar_Reflection_V2_Formula.Eq
                                       (FStar_Pervasives_Native.Some t), me1,
                                       me2)
                                      ->
                                      Obj.magic
                                        (Obj.repr
                                           (let uu___5 =
                                              let uu___6 =
                                                let uu___7 =
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___8 -> me2)) in
                                                FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.Tactics.CanonMonoid.fst"
                                                           (Prims.of_int (116))
                                                           (Prims.of_int (60))
                                                           (Prims.of_int (116))
                                                           (Prims.of_int (63)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.Tactics.CanonMonoid.fst"
                                                           (Prims.of_int (116))
                                                           (Prims.of_int (19))
                                                           (Prims.of_int (116))
                                                           (Prims.of_int (67)))))
                                                  (Obj.magic uu___7)
                                                  (fun uu___8 ->
                                                     (fun uu___8 ->
                                                        let uu___9 =
                                                          Obj.magic
                                                            (FStar_Tactics_Effect.lift_div_tac
                                                               (fun uu___10
                                                                  -> me1)) in
                                                        Obj.magic
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonMonoid.fst"
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (55)))))
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonMonoid.fst"
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (67)))))
                                                             (Obj.magic
                                                                uu___9)
                                                             (fun uu___10 ->
                                                                (fun uu___10
                                                                   ->
                                                                   let uu___11
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    Obj.magic
                                                                    (failwith
                                                                    "Cannot evaluate open quotation at runtime"))
                                                                    uu___12)) in
                                                                   Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonMonoid.fst"
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonMonoid.fst"
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (67)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_App
                                                                    ((FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["Prims";
                                                                    "squash"]))),
                                                                    ((FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_App
                                                                    ((FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_App
                                                                    ((FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_App
                                                                    ((FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["Prims";
                                                                    "eq2"]))),
                                                                    (uu___12,
                                                                    FStarC_Reflection_V2_Data.Q_Implicit)))),
                                                                    (uu___10,
                                                                    FStarC_Reflection_V2_Data.Q_Explicit)))),
                                                                    (uu___8,
                                                                    FStarC_Reflection_V2_Data.Q_Explicit)))),
                                                                    FStarC_Reflection_V2_Data.Q_Explicit)))))))
                                                                  uu___10)))
                                                       uu___8) in
                                              FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "FStar.Tactics.CanonMonoid.fst"
                                                         (Prims.of_int (116))
                                                         (Prims.of_int (19))
                                                         (Prims.of_int (116))
                                                         (Prims.of_int (67)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "FStar.Tactics.CanonMonoid.fst"
                                                         (Prims.of_int (116))
                                                         (Prims.of_int (14))
                                                         (Prims.of_int (116))
                                                         (Prims.of_int (67)))))
                                                (Obj.magic uu___6)
                                                (fun uu___7 ->
                                                   (fun uu___7 ->
                                                      Obj.magic
                                                        (FStar_Tactics_V2_Derived.tcut
                                                           uu___7)) uu___7) in
                                            FStar_Tactics_Effect.tac_bind
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "FStar.Tactics.CanonMonoid.fst"
                                                       (Prims.of_int (116))
                                                       (Prims.of_int (14))
                                                       (Prims.of_int (116))
                                                       (Prims.of_int (67)))))
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "FStar.Tactics.CanonMonoid.fst"
                                                       (Prims.of_int (117))
                                                       (Prims.of_int (6))
                                                       (Prims.of_int (126))
                                                       (Prims.of_int (49)))))
                                              (Obj.magic uu___5)
                                              (fun uu___6 ->
                                                 (fun b ->
                                                    let uu___6 =
                                                      FStar_Tactics_V2_Derived.smt
                                                        () in
                                                    Obj.magic
                                                      (FStar_Tactics_Effect.tac_bind
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "FStar.Tactics.CanonMonoid.fst"
                                                                  (Prims.of_int (117))
                                                                  (Prims.of_int (6))
                                                                  (Prims.of_int (117))
                                                                  (Prims.of_int (12)))))
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "FStar.Tactics.CanonMonoid.fst"
                                                                  (Prims.of_int (117))
                                                                  (Prims.of_int (13))
                                                                  (Prims.of_int (126))
                                                                  (Prims.of_int (49)))))
                                                         (Obj.magic uu___6)
                                                         (fun uu___7 ->
                                                            (fun uu___7 ->
                                                               let uu___8 =
                                                                 reification
                                                                   m me1 in
                                                               Obj.magic
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonMonoid.fst"
                                                                    (Prims.of_int (119))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (119))
                                                                    (Prims.of_int (32)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonMonoid.fst"
                                                                    (Prims.of_int (119))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (126))
                                                                    (Prims.of_int (49)))))
                                                                    (
                                                                    Obj.magic
                                                                    uu___8)
                                                                    (
                                                                    fun
                                                                    uu___9 ->
                                                                    (fun r1
                                                                    ->
                                                                    let uu___9
                                                                    =
                                                                    reification
                                                                    m me2 in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonMonoid.fst"
                                                                    (Prims.of_int (120))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (120))
                                                                    (Prims.of_int (32)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonMonoid.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (126))
                                                                    (Prims.of_int (49)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun r2
                                                                    ->
                                                                    let uu___10
                                                                    =
                                                                    let uu___11
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    Obj.magic
                                                                    (failwith
                                                                    "Cannot evaluate open quotation at runtime"))
                                                                    uu___12)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonMonoid.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (62)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonMonoid.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (62)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Derived.change_sq
                                                                    uu___12))
                                                                    uu___12) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonMonoid.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (62)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonMonoid.fst"
                                                                    (Prims.of_int (122))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (126))
                                                                    (Prims.of_int (49)))))
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
                                                                    FStar_Tactics_V2_Derived.apply
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "CanonMonoid";
                                                                    "monoid_reflect"]))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonMonoid.fst"
                                                                    (Prims.of_int (122))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (122))
                                                                    (Prims.of_int (29)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonMonoid.fst"
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (126))
                                                                    (Prims.of_int (49)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    Obj.magic
                                                                    (FStarC_Tactics_V2_Builtins.norm
                                                                    [
                                                                    FStar_Pervasives.delta_only
                                                                    ["FStar.Tactics.CanonMonoid.mldenote";
                                                                    "FStar.Tactics.CanonMonoid.flatten";
                                                                    "FStar.List.Tot.Base.op_At";
                                                                    "FStar.List.Tot.Base.append"]]))
                                                                    uu___13)))
                                                                    uu___11)))
                                                                    uu___10)))
                                                                    uu___9)))
                                                              uu___7)))
                                                   uu___6)))
                                  | uu___5 ->
                                      Obj.magic
                                        (Obj.repr
                                           (FStar_Tactics_V2_Derived.fail
                                              "Goal should be an equality")))
                                 uu___4))) uu___3))) uu___1)