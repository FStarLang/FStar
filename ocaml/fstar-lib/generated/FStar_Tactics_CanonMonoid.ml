open Prims
let (dump : Prims.string -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun m ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Range.mk_range "FStar.Tactics.CanonMonoid.fst"
         (Prims.of_int (24)) (Prims.of_int (16)) (Prims.of_int (24))
         (Prims.of_int (28)))
      (FStar_Range.mk_range "FStar.Tactics.CanonMonoid.fst"
         (Prims.of_int (24)) (Prims.of_int (13)) (Prims.of_int (24))
         (Prims.of_int (40)))
      (Obj.magic (FStar_Tactics_Builtins.debugging ()))
      (fun uu___ ->
         (fun uu___ ->
            if uu___
            then Obj.magic (Obj.repr (FStar_Tactics_Builtins.dump m))
            else
              Obj.magic
                (Obj.repr
                   (FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> ()))))
           uu___)
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
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.term ->
          ('a exp, unit) FStar_Tactics_Effect.tac_repr
  =
  fun mult ->
    fun unit ->
      fun me ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Range.mk_range "FStar.Tactics.CanonMonoid.fst"
             (Prims.of_int (84)) (Prims.of_int (15)) (Prims.of_int (84))
             (Prims.of_int (33)))
          (FStar_Range.mk_range "FStar.Tactics.CanonMonoid.fst"
             (Prims.of_int (83)) (Prims.of_int (71)) (Prims.of_int (84))
             (Prims.of_int (36)))
          (FStar_Tactics_Effect.lift_div_tac
             (fun uu___ -> FStar_Reflection_Derived_Lemmas.collect_app_ref me))
          (fun uu___ ->
             (fun uu___ ->
                match uu___ with
                | (hd, tl) ->
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Range.mk_range
                            "FStar.Tactics.CanonMonoid.fst"
                            (Prims.of_int (85)) (Prims.of_int (11))
                            (Prims.of_int (85)) (Prims.of_int (24)))
                         (FStar_Range.mk_range
                            "FStar.Tactics.CanonMonoid.fst"
                            (Prims.of_int (86)) (Prims.of_int (2))
                            (Prims.of_int (94)) (Prims.of_int (25)))
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___1 -> FStar_List_Tot_Base.list_unref tl))
                         (fun uu___1 ->
                            (fun tl1 ->
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Range.mk_range
                                       "FStar.Tactics.CanonMonoid.fst"
                                       (Prims.of_int (86)) (Prims.of_int (8))
                                       (Prims.of_int (86))
                                       (Prims.of_int (22)))
                                    (FStar_Range.mk_range
                                       "FStar.Tactics.CanonMonoid.fst"
                                       (Prims.of_int (86)) (Prims.of_int (2))
                                       (Prims.of_int (94))
                                       (Prims.of_int (25)))
                                    (Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Range.mk_range
                                             "FStar.Tactics.CanonMonoid.fst"
                                             (Prims.of_int (86))
                                             (Prims.of_int (8))
                                             (Prims.of_int (86))
                                             (Prims.of_int (18)))
                                          (FStar_Range.mk_range
                                             "FStar.Tactics.CanonMonoid.fst"
                                             (Prims.of_int (86))
                                             (Prims.of_int (8))
                                             (Prims.of_int (86))
                                             (Prims.of_int (22)))
                                          (Obj.magic
                                             (FStar_Tactics_Builtins.inspect
                                                hd))
                                          (fun uu___1 ->
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___2 -> (uu___1, tl1)))))
                                    (fun uu___1 ->
                                       (fun uu___1 ->
                                          match uu___1 with
                                          | (FStar_Reflection_Data.Tv_FVar
                                             fv,
                                             (me1,
                                              FStar_Reflection_Data.Q_Explicit)::
                                             (me2,
                                              FStar_Reflection_Data.Q_Explicit)::[])
                                              ->
                                              Obj.magic
                                                (FStar_Tactics_Effect.tac_bind
                                                   (FStar_Range.mk_range
                                                      "FStar.Tactics.CanonMonoid.fst"
                                                      (Prims.of_int (88))
                                                      (Prims.of_int (7))
                                                      (Prims.of_int (88))
                                                      (Prims.of_int (43)))
                                                   (FStar_Range.mk_range
                                                      "FStar.Tactics.CanonMonoid.fst"
                                                      (Prims.of_int (88))
                                                      (Prims.of_int (4))
                                                      (Prims.of_int (90))
                                                      (Prims.of_int (25)))
                                                   (Obj.magic
                                                      (FStar_Tactics_Effect.tac_bind
                                                         (FStar_Range.mk_range
                                                            "FStar.Tactics.CanonMonoid.fst"
                                                            (Prims.of_int (88))
                                                            (Prims.of_int (19))
                                                            (Prims.of_int (88))
                                                            (Prims.of_int (38)))
                                                         (FStar_Range.mk_range
                                                            "FStar.Tactics.CanonMonoid.fst"
                                                            (Prims.of_int (88))
                                                            (Prims.of_int (7))
                                                            (Prims.of_int (88))
                                                            (Prims.of_int (43)))
                                                         (Obj.magic
                                                            (FStar_Tactics_Builtins.pack
                                                               (FStar_Reflection_Data.Tv_FVar
                                                                  fv)))
                                                         (fun uu___2 ->
                                                            (fun uu___2 ->
                                                               Obj.magic
                                                                 (FStar_Tactics_Builtins.term_eq_old
                                                                    uu___2
                                                                    mult))
                                                              uu___2)))
                                                   (fun uu___2 ->
                                                      (fun uu___2 ->
                                                         if uu___2
                                                         then
                                                           Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Range.mk_range
                                                                   "FStar.Tactics.CanonMonoid.fst"
                                                                   (Prims.of_int (89))
                                                                   (Prims.of_int (14))
                                                                   (Prims.of_int (89))
                                                                   (Prims.of_int (45)))
                                                                (FStar_Range.mk_range
                                                                   "FStar.Tactics.CanonMonoid.fst"
                                                                   (Prims.of_int (89))
                                                                   (Prims.of_int (9))
                                                                   (Prims.of_int (89))
                                                                   (Prims.of_int (77)))
                                                                (Obj.magic
                                                                   (reification_aux
                                                                    mult unit
                                                                    me1))
                                                                (fun uu___3
                                                                   ->
                                                                   (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonMonoid.fst"
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (77)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonMonoid.fst"
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (89))
                                                                    (Prims.of_int (77)))
                                                                    (Obj.magic
                                                                    (reification_aux
                                                                    mult unit
                                                                    me2))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Mult
                                                                    (uu___3,
                                                                    uu___4)))))
                                                                    uu___3))
                                                         else
                                                           Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Range.mk_range
                                                                   "FStar.Tactics.CanonMonoid.fst"
                                                                   (Prims.of_int (90))
                                                                   (Prims.of_int (13))
                                                                   (Prims.of_int (90))
                                                                   (Prims.of_int (25)))
                                                                (FStar_Range.mk_range
                                                                   "FStar.Tactics.CanonMonoid.fst"
                                                                   (Prims.of_int (90))
                                                                   (Prims.of_int (9))
                                                                   (Prims.of_int (90))
                                                                   (Prims.of_int (25)))
                                                                (Obj.magic
                                                                   (FStar_Tactics_Builtins.unquote
                                                                    me))
                                                                (fun uu___4
                                                                   ->
                                                                   FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Var
                                                                    uu___4))))
                                                        uu___2))
                                          | (uu___2, uu___3) ->
                                              Obj.magic
                                                (FStar_Tactics_Effect.tac_bind
                                                   (FStar_Range.mk_range
                                                      "FStar.Tactics.CanonMonoid.fst"
                                                      (Prims.of_int (92))
                                                      (Prims.of_int (7))
                                                      (Prims.of_int (92))
                                                      (Prims.of_int (26)))
                                                   (FStar_Range.mk_range
                                                      "FStar.Tactics.CanonMonoid.fst"
                                                      (Prims.of_int (92))
                                                      (Prims.of_int (4))
                                                      (Prims.of_int (94))
                                                      (Prims.of_int (25)))
                                                   (Obj.magic
                                                      (FStar_Tactics_Builtins.term_eq_old
                                                         me unit))
                                                   (fun uu___4 ->
                                                      (fun uu___4 ->
                                                         if uu___4
                                                         then
                                                           Obj.magic
                                                             (Obj.repr
                                                                (FStar_Tactics_Effect.lift_div_tac
                                                                   (fun
                                                                    uu___5 ->
                                                                    Unit)))
                                                         else
                                                           Obj.magic
                                                             (Obj.repr
                                                                (FStar_Tactics_Effect.tac_bind
                                                                   (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonMonoid.fst"
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (25)))
                                                                   (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonMonoid.fst"
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (25)))
                                                                   (Obj.magic
                                                                    (FStar_Tactics_Builtins.unquote
                                                                    me))
                                                                   (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    Var
                                                                    uu___6)))))
                                                        uu___4))) uu___1)))
                              uu___1))) uu___)
let reification :
  'a .
    'a FStar_Algebra_Monoid.monoid ->
      FStar_Reflection_Types.term ->
        ('a exp, unit) FStar_Tactics_Effect.tac_repr
  =
  fun m ->
    fun me ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Range.mk_range "FStar.Tactics.CanonMonoid.fst"
           (Prims.of_int (97)) (Prims.of_int (15)) (Prims.of_int (97))
           (Prims.of_int (67)))
        (FStar_Range.mk_range "FStar.Tactics.CanonMonoid.fst"
           (Prims.of_int (97)) (Prims.of_int (70)) (Prims.of_int (98))
           (Prims.of_int (70)))
        (Obj.magic
           (FStar_Tactics_Effect.tac_bind
              (FStar_Range.mk_range "FStar.Tactics.CanonMonoid.fst"
                 (Prims.of_int (97)) (Prims.of_int (43)) (Prims.of_int (97))
                 (Prims.of_int (67)))
              (FStar_Range.mk_range "FStar.Tactics.CanonMonoid.fst"
                 (Prims.of_int (97)) (Prims.of_int (15)) (Prims.of_int (97))
                 (Prims.of_int (67)))
              (FStar_Tactics_Effect.lift_div_tac
                 (fun uu___ ->
                    (fun uu___ ->
                       Obj.magic
                         (failwith
                            "Cannot evaluate open quotation at runtime"))
                      uu___))
              (fun uu___ ->
                 (fun uu___ ->
                    Obj.magic
                      (FStar_Tactics_Derived.norm_term
                         [FStar_Pervasives.delta;
                         FStar_Pervasives.zeta;
                         FStar_Pervasives.iota] uu___)) uu___)))
        (fun uu___ ->
           (fun mult ->
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Range.mk_range "FStar.Tactics.CanonMonoid.fst"
                      (Prims.of_int (98)) (Prims.of_int (15))
                      (Prims.of_int (98)) (Prims.of_int (67)))
                   (FStar_Range.mk_range "FStar.Tactics.CanonMonoid.fst"
                      (Prims.of_int (98)) (Prims.of_int (70))
                      (Prims.of_int (99)) (Prims.of_int (48)))
                   (Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Range.mk_range
                            "FStar.Tactics.CanonMonoid.fst"
                            (Prims.of_int (98)) (Prims.of_int (43))
                            (Prims.of_int (98)) (Prims.of_int (67)))
                         (FStar_Range.mk_range
                            "FStar.Tactics.CanonMonoid.fst"
                            (Prims.of_int (98)) (Prims.of_int (15))
                            (Prims.of_int (98)) (Prims.of_int (67)))
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___ ->
                               (fun uu___ ->
                                  Obj.magic
                                    (failwith
                                       "Cannot evaluate open quotation at runtime"))
                                 uu___))
                         (fun uu___ ->
                            (fun uu___ ->
                               Obj.magic
                                 (FStar_Tactics_Derived.norm_term
                                    [FStar_Pervasives.delta;
                                    FStar_Pervasives.zeta;
                                    FStar_Pervasives.iota] uu___)) uu___)))
                   (fun uu___ ->
                      (fun unit ->
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Range.mk_range
                                 "FStar.Tactics.CanonMonoid.fst"
                                 (Prims.of_int (99)) (Prims.of_int (15))
                                 (Prims.of_int (99)) (Prims.of_int (45)))
                              (FStar_Range.mk_range
                                 "FStar.Tactics.CanonMonoid.fst"
                                 (Prims.of_int (103)) (Prims.of_int (4))
                                 (Prims.of_int (103)) (Prims.of_int (32)))
                              (Obj.magic
                                 (FStar_Tactics_Derived.norm_term
                                    [FStar_Pervasives.delta;
                                    FStar_Pervasives.zeta;
                                    FStar_Pervasives.iota] me))
                              (fun uu___ ->
                                 (fun me1 ->
                                    Obj.magic (reification_aux mult unit me1))
                                   uu___))) uu___))) uu___)
let canon_monoid :
  'a .
    'a FStar_Algebra_Monoid.monoid ->
      (unit, unit) FStar_Tactics_Effect.tac_repr
  =
  fun m ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Range.mk_range "FStar.Tactics.CanonMonoid.fst"
         (Prims.of_int (106)) (Prims.of_int (2)) (Prims.of_int (106))
         (Prims.of_int (9)))
      (FStar_Range.mk_range "FStar.Tactics.CanonMonoid.fst"
         (Prims.of_int (106)) (Prims.of_int (10)) (Prims.of_int (107))
         (Prims.of_int (24))) (Obj.magic (FStar_Tactics_Builtins.norm []))
      (fun uu___ ->
         (fun uu___ ->
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Range.mk_range "FStar.Tactics.CanonMonoid.fst"
                    (Prims.of_int (107)) (Prims.of_int (10))
                    (Prims.of_int (107)) (Prims.of_int (21)))
                 (FStar_Range.mk_range "FStar.Tactics.CanonMonoid.fst"
                    (Prims.of_int (108)) (Prims.of_int (2))
                    (Prims.of_int (120)) (Prims.of_int (42)))
                 (Obj.magic (FStar_Tactics_Derived.cur_goal ()))
                 (fun uu___1 ->
                    (fun g ->
                       Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Range.mk_range
                               "FStar.Tactics.CanonMonoid.fst"
                               (Prims.of_int (108)) (Prims.of_int (8))
                               (Prims.of_int (108)) (Prims.of_int (25)))
                            (FStar_Range.mk_range
                               "FStar.Tactics.CanonMonoid.fst"
                               (Prims.of_int (108)) (Prims.of_int (2))
                               (Prims.of_int (120)) (Prims.of_int (42)))
                            (Obj.magic
                               (FStar_Reflection_Formula.term_as_formula g))
                            (fun uu___1 ->
                               (fun uu___1 ->
                                  match uu___1 with
                                  | FStar_Reflection_Formula.Comp
                                      (FStar_Reflection_Formula.Eq
                                       (FStar_Pervasives_Native.Some t), me1,
                                       me2)
                                      ->
                                      Obj.magic
                                        (Obj.repr
                                           (FStar_Tactics_Effect.tac_bind
                                              (FStar_Range.mk_range
                                                 "FStar.Tactics.CanonMonoid.fst"
                                                 (Prims.of_int (110))
                                                 (Prims.of_int (9))
                                                 (Prims.of_int (110))
                                                 (Prims.of_int (32)))
                                              (FStar_Range.mk_range
                                                 "FStar.Tactics.CanonMonoid.fst"
                                                 (Prims.of_int (110))
                                                 (Prims.of_int (6))
                                                 (Prims.of_int (119))
                                                 (Prims.of_int (69)))
                                              (Obj.magic
                                                 (FStar_Tactics_Effect.tac_bind
                                                    (FStar_Range.mk_range
                                                       "FStar.Tactics.CanonMonoid.fst"
                                                       (Prims.of_int (110))
                                                       (Prims.of_int (23))
                                                       (Prims.of_int (110))
                                                       (Prims.of_int (32)))
                                                    (FStar_Range.mk_range
                                                       "FStar.Tactics.CanonMonoid.fst"
                                                       (Prims.of_int (110))
                                                       (Prims.of_int (9))
                                                       (Prims.of_int (110))
                                                       (Prims.of_int (32)))
                                                    (FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___2 ->
                                                          (fun uu___2 ->
                                                             Obj.magic
                                                               (failwith
                                                                  "Cannot evaluate open quotation at runtime"))
                                                            uu___2))
                                                    (fun uu___2 ->
                                                       (fun uu___2 ->
                                                          Obj.magic
                                                            (FStar_Tactics_Builtins.term_eq_old
                                                               t uu___2))
                                                         uu___2)))
                                              (fun uu___2 ->
                                                 (fun uu___2 ->
                                                    if uu___2
                                                    then
                                                      Obj.magic
                                                        (Obj.repr
                                                           (FStar_Tactics_Effect.tac_bind
                                                              (FStar_Range.mk_range
                                                                 "FStar.Tactics.CanonMonoid.fst"
                                                                 (Prims.of_int (111))
                                                                 (Prims.of_int (17))
                                                                 (Prims.of_int (111))
                                                                 (Prims.of_int (34)))
                                                              (FStar_Range.mk_range
                                                                 "FStar.Tactics.CanonMonoid.fst"
                                                                 (Prims.of_int (111))
                                                                 (Prims.of_int (37))
                                                                 (Prims.of_int (112))
                                                                 (Prims.of_int (37)))
                                                              (Obj.magic
                                                                 (reification
                                                                    m me1))
                                                              (fun uu___3 ->
                                                                 (fun r1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonMonoid.fst"
                                                                    (Prims.of_int (112))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (112))
                                                                    (Prims.of_int (34)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonMonoid.fst"
                                                                    (Prims.of_int (113))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (51)))
                                                                    (Obj.magic
                                                                    (reification
                                                                    m me2))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun r2
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonMonoid.fst"
                                                                    (Prims.of_int (113))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (113))
                                                                    (Prims.of_int (56)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonMonoid.fst"
                                                                    (Prims.of_int (114))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (51)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonMonoid.fst"
                                                                    (Prims.of_int (113))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (113))
                                                                    (Prims.of_int (56)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonMonoid.fst"
                                                                    (Prims.of_int (113))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (113))
                                                                    (Prims.of_int (56)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (failwith
                                                                    "Cannot evaluate open quotation at runtime"))
                                                                    uu___3))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Derived.change_sq
                                                                    uu___3))
                                                                    uu___3)))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonMonoid.fst"
                                                                    (Prims.of_int (114))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (114))
                                                                    (Prims.of_int (31)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.CanonMonoid.fst"
                                                                    (Prims.of_int (115))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (51)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Derived.apply
                                                                    (FStar_Reflection_Builtins.pack_ln
                                                                    (FStar_Reflection_Data.Tv_FVar
                                                                    (FStar_Reflection_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "CanonMonoid";
                                                                    "monoid_reflect"])))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Builtins.norm
                                                                    [
                                                                    FStar_Pervasives.delta_only
                                                                    ["FStar.Tactics.CanonMonoid.mldenote";
                                                                    "FStar.Tactics.CanonMonoid.flatten";
                                                                    "FStar.List.Tot.Base.op_At";
                                                                    "FStar.List.Tot.Base.append"]]))
                                                                    uu___4)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                   uu___3)))
                                                    else
                                                      Obj.magic
                                                        (Obj.repr
                                                           (FStar_Tactics_Derived.fail
                                                              "Goal should be an equality at the right monoid type")))
                                                   uu___2)))
                                  | uu___2 ->
                                      Obj.magic
                                        (Obj.repr
                                           (FStar_Tactics_Derived.fail
                                              "Goal should be an equality")))
                                 uu___1))) uu___1))) uu___)