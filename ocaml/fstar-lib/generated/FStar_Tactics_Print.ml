open Prims
let (paren : Prims.string -> Prims.string) =
  fun s -> Prims.strcat "(" (Prims.strcat s ")")
let (bv_to_string :
  FStar_Reflection_Types.bv ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun bv ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Range.mk_range "FStar.Tactics.Print.fst" (Prims.of_int (13))
         (Prims.of_int (14)) (Prims.of_int (13)) (Prims.of_int (27)))
      (FStar_Range.mk_range "FStar.Tactics.Print.fst" (Prims.of_int (14))
         (Prims.of_int (4)) (Prims.of_int (14)) (Prims.of_int (64)))
      (FStar_Tactics_Effect.lift_div_tac
         (fun uu___ -> FStar_Reflection_Builtins.inspect_bv bv))
      (fun uu___ ->
         (fun bvv ->
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                    (Prims.of_int (14)) (Prims.of_int (10))
                    (Prims.of_int (14)) (Prims.of_int (64)))
                 (FStar_Range.mk_range "prims.fst" (Prims.of_int (606))
                    (Prims.of_int (19)) (Prims.of_int (606))
                    (Prims.of_int (31)))
                 (Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                          (Prims.of_int (14)) (Prims.of_int (10))
                          (Prims.of_int (14)) (Prims.of_int (23)))
                       (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                          (Prims.of_int (14)) (Prims.of_int (10))
                          (Prims.of_int (14)) (Prims.of_int (64)))
                       (Obj.magic (FStar_Tactics_Derived.name_of_bv bv))
                       (fun uu___ ->
                          (fun uu___ ->
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                                     (Prims.of_int (14)) (Prims.of_int (26))
                                     (Prims.of_int (14)) (Prims.of_int (64)))
                                  (FStar_Range.mk_range "prims.fst"
                                     (Prims.of_int (606)) (Prims.of_int (19))
                                     (Prims.of_int (606)) (Prims.of_int (31)))
                                  (Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Range.mk_range
                                           "FStar.Tactics.Print.fst"
                                           (Prims.of_int (14))
                                           (Prims.of_int (32))
                                           (Prims.of_int (14))
                                           (Prims.of_int (64)))
                                        (FStar_Range.mk_range "prims.fst"
                                           (Prims.of_int (606))
                                           (Prims.of_int (19))
                                           (Prims.of_int (606))
                                           (Prims.of_int (31)))
                                        (Obj.magic
                                           (FStar_Tactics_Effect.tac_bind
                                              (FStar_Range.mk_range
                                                 "FStar.Tactics.Print.fst"
                                                 (Prims.of_int (14))
                                                 (Prims.of_int (32))
                                                 (Prims.of_int (14))
                                                 (Prims.of_int (58)))
                                              (FStar_Range.mk_range "prims.fst"
                                                 (Prims.of_int (606))
                                                 (Prims.of_int (19))
                                                 (Prims.of_int (606))
                                                 (Prims.of_int (31)))
                                              (Obj.magic
                                                 (FStar_Tactics_Builtins.term_to_string
                                                    bvv.FStar_Reflection_Data.bv_sort))
                                              (fun uu___1 ->
                                                 FStar_Tactics_Effect.lift_div_tac
                                                   (fun uu___2 ->
                                                      Prims.strcat uu___1 ")"))))
                                        (fun uu___1 ->
                                           FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___2 ->
                                                Prims.strcat ":" uu___1))))
                                  (fun uu___1 ->
                                     FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___2 ->
                                          Prims.strcat uu___ uu___1)))) uu___)))
                 (fun uu___ ->
                    FStar_Tactics_Effect.lift_div_tac
                      (fun uu___1 -> Prims.strcat "(" uu___)))) uu___)
let rec print_list_aux :
  'a .
    ('a -> (Prims.string, unit) FStar_Tactics_Effect.tac_repr) ->
      'a Prims.list -> (Prims.string, unit) FStar_Tactics_Effect.tac_repr
  =
  fun uu___1 ->
    fun uu___ ->
      (fun f ->
         fun xs ->
           match xs with
           | [] ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> "")))
           | x::[] -> Obj.magic (Obj.repr (f x))
           | x::xs1 ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                          (Prims.of_int (22)) (Prims.of_int (13))
                          (Prims.of_int (22)) (Prims.of_int (16)))
                       (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                          (Prims.of_int (22)) (Prims.of_int (13))
                          (Prims.of_int (22)) (Prims.of_int (45)))
                       (Obj.magic (f x))
                       (fun uu___ ->
                          (fun uu___ ->
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                                     (Prims.of_int (22)) (Prims.of_int (19))
                                     (Prims.of_int (22)) (Prims.of_int (45)))
                                  (FStar_Range.mk_range "prims.fst"
                                     (Prims.of_int (606)) (Prims.of_int (19))
                                     (Prims.of_int (606)) (Prims.of_int (31)))
                                  (Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Range.mk_range
                                           "FStar.Tactics.Print.fst"
                                           (Prims.of_int (22))
                                           (Prims.of_int (26))
                                           (Prims.of_int (22))
                                           (Prims.of_int (45)))
                                        (FStar_Range.mk_range "prims.fst"
                                           (Prims.of_int (606))
                                           (Prims.of_int (19))
                                           (Prims.of_int (606))
                                           (Prims.of_int (31)))
                                        (Obj.magic (print_list_aux f xs1))
                                        (fun uu___1 ->
                                           FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___2 ->
                                                Prims.strcat "; " uu___1))))
                                  (fun uu___1 ->
                                     FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___2 ->
                                          Prims.strcat uu___ uu___1)))) uu___))))
        uu___1 uu___
let print_list :
  'a .
    ('a -> (Prims.string, unit) FStar_Tactics_Effect.tac_repr) ->
      'a Prims.list -> (Prims.string, unit) FStar_Tactics_Effect.tac_repr
  =
  fun f ->
    fun l ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Range.mk_range "FStar.Tactics.Print.fst" (Prims.of_int (26))
           (Prims.of_int (9)) (Prims.of_int (26)) (Prims.of_int (33)))
        (FStar_Range.mk_range "prims.fst" (Prims.of_int (606)) (Prims.of_int (19))
           (Prims.of_int (606)) (Prims.of_int (31)))
        (Obj.magic
           (FStar_Tactics_Effect.tac_bind
              (FStar_Range.mk_range "FStar.Tactics.Print.fst" (Prims.of_int (26))
                 (Prims.of_int (9)) (Prims.of_int (26)) (Prims.of_int (27)))
              (FStar_Range.mk_range "prims.fst" (Prims.of_int (606))
                 (Prims.of_int (19)) (Prims.of_int (606)) (Prims.of_int (31)))
              (Obj.magic (print_list_aux f l))
              (fun uu___ ->
                 FStar_Tactics_Effect.lift_div_tac
                   (fun uu___1 -> Prims.strcat uu___ "]"))))
        (fun uu___ ->
           FStar_Tactics_Effect.lift_div_tac
             (fun uu___1 -> Prims.strcat "[" uu___))
let rec (universe_to_ast_string :
  FStar_Reflection_Types.universe ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    (fun u ->
       match FStar_Reflection_Builtins.inspect_universe u with
       | FStar_Reflection_Data.Uv_Zero ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> "Uv_Zero")))
       | FStar_Reflection_Data.Uv_Succ u1 ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                      (Prims.of_int (31)) (Prims.of_int (29))
                      (Prims.of_int (31)) (Prims.of_int (61)))
                   (FStar_Range.mk_range "prims.fst" (Prims.of_int (606))
                      (Prims.of_int (19)) (Prims.of_int (606))
                      (Prims.of_int (31)))
                   (Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                            (Prims.of_int (31)) (Prims.of_int (35))
                            (Prims.of_int (31)) (Prims.of_int (61)))
                         (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                            (Prims.of_int (31)) (Prims.of_int (29))
                            (Prims.of_int (31)) (Prims.of_int (61)))
                         (Obj.magic (universe_to_ast_string u1))
                         (fun uu___ ->
                            FStar_Tactics_Effect.lift_div_tac
                              (fun uu___1 -> paren uu___))))
                   (fun uu___ ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___1 -> Prims.strcat "Uv_Succ" uu___))))
       | FStar_Reflection_Data.Uv_Max us ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                      (Prims.of_int (32)) (Prims.of_int (28))
                      (Prims.of_int (32)) (Prims.of_int (64)))
                   (FStar_Range.mk_range "prims.fst" (Prims.of_int (606))
                      (Prims.of_int (19)) (Prims.of_int (606))
                      (Prims.of_int (31)))
                   (Obj.magic (print_list universe_to_ast_string us))
                   (fun uu___ ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___1 -> Prims.strcat "Uv_Max" uu___))))
       | FStar_Reflection_Data.Uv_BVar n ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___ ->
                      Prims.strcat "Uv_BVar" (paren (Prims.string_of_int n)))))
       | FStar_Reflection_Data.Uv_Name i ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___ ->
                      Prims.strcat "Uv_Name"
                        (paren (FStar_Pervasives_Native.fst i)))))
       | FStar_Reflection_Data.Uv_Unif uu___ ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> "Uv_Unif")))
       | FStar_Reflection_Data.Uv_Unk ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> "Uv_Unk"))))
      uu___
let (universes_to_ast_string :
  FStar_Reflection_Data.universes ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  = fun us -> print_list universe_to_ast_string us
let rec (term_to_ast_string :
  FStar_Reflection_Types.term ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Range.mk_range "FStar.Tactics.Print.fst" (Prims.of_int (42))
         (Prims.of_int (8)) (Prims.of_int (42)) (Prims.of_int (17)))
      (FStar_Range.mk_range "FStar.Tactics.Print.fst" (Prims.of_int (42))
         (Prims.of_int (2)) (Prims.of_int (70)) (Prims.of_int (21)))
      (Obj.magic (FStar_Tactics_Builtins.inspect t))
      (fun uu___ ->
         (fun uu___ ->
            match uu___ with
            | FStar_Reflection_Data.Tv_Var bv ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.tac_bind
                        (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                           (Prims.of_int (43)) (Prims.of_int (29))
                           (Prims.of_int (43)) (Prims.of_int (44)))
                        (FStar_Range.mk_range "prims.fst" (Prims.of_int (606))
                           (Prims.of_int (19)) (Prims.of_int (606))
                           (Prims.of_int (31))) (Obj.magic (bv_to_string bv))
                        (fun uu___1 ->
                           FStar_Tactics_Effect.lift_div_tac
                             (fun uu___2 -> Prims.strcat "Tv_Var " uu___1))))
            | FStar_Reflection_Data.Tv_BVar bv ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.tac_bind
                        (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                           (Prims.of_int (44)) (Prims.of_int (31))
                           (Prims.of_int (44)) (Prims.of_int (46)))
                        (FStar_Range.mk_range "prims.fst" (Prims.of_int (606))
                           (Prims.of_int (19)) (Prims.of_int (606))
                           (Prims.of_int (31))) (Obj.magic (bv_to_string bv))
                        (fun uu___1 ->
                           FStar_Tactics_Effect.lift_div_tac
                             (fun uu___2 -> Prims.strcat "Tv_BVar " uu___1))))
            | FStar_Reflection_Data.Tv_FVar fv ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___1 ->
                           Prims.strcat "Tv_FVar "
                             (FStar_Reflection_Derived.fv_to_string fv))))
            | FStar_Reflection_Data.Tv_UInst (fv, us) ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.tac_bind
                        (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                           (Prims.of_int (47)) (Prims.of_int (17))
                           (Prims.of_int (47)) (Prims.of_int (76)))
                        (FStar_Range.mk_range "prims.fst" (Prims.of_int (606))
                           (Prims.of_int (19)) (Prims.of_int (606))
                           (Prims.of_int (31)))
                        (Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                                 (Prims.of_int (47)) (Prims.of_int (23))
                                 (Prims.of_int (47)) (Prims.of_int (76)))
                              (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                                 (Prims.of_int (47)) (Prims.of_int (17))
                                 (Prims.of_int (47)) (Prims.of_int (76)))
                              (Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                                       (Prims.of_int (47))
                                       (Prims.of_int (42))
                                       (Prims.of_int (47))
                                       (Prims.of_int (75)))
                                    (FStar_Range.mk_range "prims.fst"
                                       (Prims.of_int (606))
                                       (Prims.of_int (19))
                                       (Prims.of_int (606))
                                       (Prims.of_int (31)))
                                    (Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Range.mk_range
                                             "FStar.Tactics.Print.fst"
                                             (Prims.of_int (47))
                                             (Prims.of_int (49))
                                             (Prims.of_int (47))
                                             (Prims.of_int (75)))
                                          (FStar_Range.mk_range "prims.fst"
                                             (Prims.of_int (606))
                                             (Prims.of_int (19))
                                             (Prims.of_int (606))
                                             (Prims.of_int (31)))
                                          (Obj.magic
                                             (universes_to_ast_string us))
                                          (fun uu___1 ->
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___2 ->
                                                  Prims.strcat ", " uu___1))))
                                    (fun uu___1 ->
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___2 ->
                                            Prims.strcat
                                              (FStar_Reflection_Derived.fv_to_string
                                                 fv) uu___1))))
                              (fun uu___1 ->
                                 FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___2 -> paren uu___1))))
                        (fun uu___1 ->
                           FStar_Tactics_Effect.lift_div_tac
                             (fun uu___2 -> Prims.strcat "Tv_UInst" uu___1))))
            | FStar_Reflection_Data.Tv_App (hd, (a, uu___1)) ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.tac_bind
                        (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                           (Prims.of_int (48)) (Prims.of_int (36))
                           (Prims.of_int (48)) (Prims.of_int (95)))
                        (FStar_Range.mk_range "prims.fst" (Prims.of_int (606))
                           (Prims.of_int (19)) (Prims.of_int (606))
                           (Prims.of_int (31)))
                        (Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                                 (Prims.of_int (48)) (Prims.of_int (42))
                                 (Prims.of_int (48)) (Prims.of_int (95)))
                              (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                                 (Prims.of_int (48)) (Prims.of_int (36))
                                 (Prims.of_int (48)) (Prims.of_int (95)))
                              (Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                                       (Prims.of_int (48))
                                       (Prims.of_int (43))
                                       (Prims.of_int (48))
                                       (Prims.of_int (64)))
                                    (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                                       (Prims.of_int (48))
                                       (Prims.of_int (42))
                                       (Prims.of_int (48))
                                       (Prims.of_int (95)))
                                    (Obj.magic (term_to_ast_string hd))
                                    (fun uu___2 ->
                                       (fun uu___2 ->
                                          Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Range.mk_range
                                                  "FStar.Tactics.Print.fst"
                                                  (Prims.of_int (48))
                                                  (Prims.of_int (67))
                                                  (Prims.of_int (48))
                                                  (Prims.of_int (94)))
                                               (FStar_Range.mk_range "prims.fst"
                                                  (Prims.of_int (606))
                                                  (Prims.of_int (19))
                                                  (Prims.of_int (606))
                                                  (Prims.of_int (31)))
                                               (Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Range.mk_range
                                                        "FStar.Tactics.Print.fst"
                                                        (Prims.of_int (48))
                                                        (Prims.of_int (74))
                                                        (Prims.of_int (48))
                                                        (Prims.of_int (94)))
                                                     (FStar_Range.mk_range
                                                        "prims.fst"
                                                        (Prims.of_int (606))
                                                        (Prims.of_int (19))
                                                        (Prims.of_int (606))
                                                        (Prims.of_int (31)))
                                                     (Obj.magic
                                                        (term_to_ast_string a))
                                                     (fun uu___3 ->
                                                        FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___4 ->
                                                             Prims.strcat
                                                               ", " uu___3))))
                                               (fun uu___3 ->
                                                  FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___4 ->
                                                       Prims.strcat uu___2
                                                         uu___3)))) uu___2)))
                              (fun uu___2 ->
                                 FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___3 -> paren uu___2))))
                        (fun uu___2 ->
                           FStar_Tactics_Effect.lift_div_tac
                             (fun uu___3 -> Prims.strcat "Tv_App " uu___2))))
            | FStar_Reflection_Data.Tv_Abs (x, e) ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.tac_bind
                        (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                           (Prims.of_int (49)) (Prims.of_int (30))
                           (Prims.of_int (49)) (Prims.of_int (86)))
                        (FStar_Range.mk_range "prims.fst" (Prims.of_int (606))
                           (Prims.of_int (19)) (Prims.of_int (606))
                           (Prims.of_int (31)))
                        (Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                                 (Prims.of_int (49)) (Prims.of_int (36))
                                 (Prims.of_int (49)) (Prims.of_int (86)))
                              (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                                 (Prims.of_int (49)) (Prims.of_int (30))
                                 (Prims.of_int (49)) (Prims.of_int (86)))
                              (Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                                       (Prims.of_int (49))
                                       (Prims.of_int (37))
                                       (Prims.of_int (49))
                                       (Prims.of_int (55)))
                                    (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                                       (Prims.of_int (49))
                                       (Prims.of_int (36))
                                       (Prims.of_int (49))
                                       (Prims.of_int (86)))
                                    (Obj.magic
                                       (FStar_Tactics_Derived.binder_to_string
                                          x))
                                    (fun uu___1 ->
                                       (fun uu___1 ->
                                          Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Range.mk_range
                                                  "FStar.Tactics.Print.fst"
                                                  (Prims.of_int (49))
                                                  (Prims.of_int (58))
                                                  (Prims.of_int (49))
                                                  (Prims.of_int (85)))
                                               (FStar_Range.mk_range "prims.fst"
                                                  (Prims.of_int (606))
                                                  (Prims.of_int (19))
                                                  (Prims.of_int (606))
                                                  (Prims.of_int (31)))
                                               (Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Range.mk_range
                                                        "FStar.Tactics.Print.fst"
                                                        (Prims.of_int (49))
                                                        (Prims.of_int (65))
                                                        (Prims.of_int (49))
                                                        (Prims.of_int (85)))
                                                     (FStar_Range.mk_range
                                                        "prims.fst"
                                                        (Prims.of_int (606))
                                                        (Prims.of_int (19))
                                                        (Prims.of_int (606))
                                                        (Prims.of_int (31)))
                                                     (Obj.magic
                                                        (term_to_ast_string e))
                                                     (fun uu___2 ->
                                                        FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___3 ->
                                                             Prims.strcat
                                                               ", " uu___2))))
                                               (fun uu___2 ->
                                                  FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___3 ->
                                                       Prims.strcat uu___1
                                                         uu___2)))) uu___1)))
                              (fun uu___1 ->
                                 FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___2 -> paren uu___1))))
                        (fun uu___1 ->
                           FStar_Tactics_Effect.lift_div_tac
                             (fun uu___2 -> Prims.strcat "Tv_Abs " uu___1))))
            | FStar_Reflection_Data.Tv_Arrow (x, c) ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.tac_bind
                        (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                           (Prims.of_int (50)) (Prims.of_int (34))
                           (Prims.of_int (50)) (Prims.of_int (90)))
                        (FStar_Range.mk_range "prims.fst" (Prims.of_int (606))
                           (Prims.of_int (19)) (Prims.of_int (606))
                           (Prims.of_int (31)))
                        (Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                                 (Prims.of_int (50)) (Prims.of_int (40))
                                 (Prims.of_int (50)) (Prims.of_int (90)))
                              (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                                 (Prims.of_int (50)) (Prims.of_int (34))
                                 (Prims.of_int (50)) (Prims.of_int (90)))
                              (Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                                       (Prims.of_int (50))
                                       (Prims.of_int (41))
                                       (Prims.of_int (50))
                                       (Prims.of_int (59)))
                                    (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                                       (Prims.of_int (50))
                                       (Prims.of_int (40))
                                       (Prims.of_int (50))
                                       (Prims.of_int (90)))
                                    (Obj.magic
                                       (FStar_Tactics_Derived.binder_to_string
                                          x))
                                    (fun uu___1 ->
                                       (fun uu___1 ->
                                          Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Range.mk_range
                                                  "FStar.Tactics.Print.fst"
                                                  (Prims.of_int (50))
                                                  (Prims.of_int (62))
                                                  (Prims.of_int (50))
                                                  (Prims.of_int (89)))
                                               (FStar_Range.mk_range "prims.fst"
                                                  (Prims.of_int (606))
                                                  (Prims.of_int (19))
                                                  (Prims.of_int (606))
                                                  (Prims.of_int (31)))
                                               (Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Range.mk_range
                                                        "FStar.Tactics.Print.fst"
                                                        (Prims.of_int (50))
                                                        (Prims.of_int (69))
                                                        (Prims.of_int (50))
                                                        (Prims.of_int (89)))
                                                     (FStar_Range.mk_range
                                                        "prims.fst"
                                                        (Prims.of_int (606))
                                                        (Prims.of_int (19))
                                                        (Prims.of_int (606))
                                                        (Prims.of_int (31)))
                                                     (Obj.magic
                                                        (comp_to_ast_string c))
                                                     (fun uu___2 ->
                                                        FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___3 ->
                                                             Prims.strcat
                                                               ", " uu___2))))
                                               (fun uu___2 ->
                                                  FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___3 ->
                                                       Prims.strcat uu___1
                                                         uu___2)))) uu___1)))
                              (fun uu___1 ->
                                 FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___2 -> paren uu___1))))
                        (fun uu___1 ->
                           FStar_Tactics_Effect.lift_div_tac
                             (fun uu___2 -> Prims.strcat "Tv_Arrow " uu___1))))
            | FStar_Reflection_Data.Tv_Type u ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.tac_bind
                        (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                           (Prims.of_int (51)) (Prims.of_int (26))
                           (Prims.of_int (51)) (Prims.of_int (58)))
                        (FStar_Range.mk_range "prims.fst" (Prims.of_int (606))
                           (Prims.of_int (19)) (Prims.of_int (606))
                           (Prims.of_int (31)))
                        (Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                                 (Prims.of_int (51)) (Prims.of_int (32))
                                 (Prims.of_int (51)) (Prims.of_int (58)))
                              (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                                 (Prims.of_int (51)) (Prims.of_int (26))
                                 (Prims.of_int (51)) (Prims.of_int (58)))
                              (Obj.magic (universe_to_ast_string u))
                              (fun uu___1 ->
                                 FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___2 -> paren uu___1))))
                        (fun uu___1 ->
                           FStar_Tactics_Effect.lift_div_tac
                             (fun uu___2 -> Prims.strcat "Type" uu___1))))
            | FStar_Reflection_Data.Tv_Refine (x, e) ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.tac_bind
                        (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                           (Prims.of_int (52)) (Prims.of_int (36))
                           (Prims.of_int (52)) (Prims.of_int (88)))
                        (FStar_Range.mk_range "prims.fst" (Prims.of_int (606))
                           (Prims.of_int (19)) (Prims.of_int (606))
                           (Prims.of_int (31)))
                        (Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                                 (Prims.of_int (52)) (Prims.of_int (42))
                                 (Prims.of_int (52)) (Prims.of_int (88)))
                              (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                                 (Prims.of_int (52)) (Prims.of_int (36))
                                 (Prims.of_int (52)) (Prims.of_int (88)))
                              (Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                                       (Prims.of_int (52))
                                       (Prims.of_int (43))
                                       (Prims.of_int (52))
                                       (Prims.of_int (57)))
                                    (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                                       (Prims.of_int (52))
                                       (Prims.of_int (42))
                                       (Prims.of_int (52))
                                       (Prims.of_int (88)))
                                    (Obj.magic (bv_to_string x))
                                    (fun uu___1 ->
                                       (fun uu___1 ->
                                          Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Range.mk_range
                                                  "FStar.Tactics.Print.fst"
                                                  (Prims.of_int (52))
                                                  (Prims.of_int (60))
                                                  (Prims.of_int (52))
                                                  (Prims.of_int (87)))
                                               (FStar_Range.mk_range "prims.fst"
                                                  (Prims.of_int (606))
                                                  (Prims.of_int (19))
                                                  (Prims.of_int (606))
                                                  (Prims.of_int (31)))
                                               (Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Range.mk_range
                                                        "FStar.Tactics.Print.fst"
                                                        (Prims.of_int (52))
                                                        (Prims.of_int (67))
                                                        (Prims.of_int (52))
                                                        (Prims.of_int (87)))
                                                     (FStar_Range.mk_range
                                                        "prims.fst"
                                                        (Prims.of_int (606))
                                                        (Prims.of_int (19))
                                                        (Prims.of_int (606))
                                                        (Prims.of_int (31)))
                                                     (Obj.magic
                                                        (term_to_ast_string e))
                                                     (fun uu___2 ->
                                                        FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___3 ->
                                                             Prims.strcat
                                                               ", " uu___2))))
                                               (fun uu___2 ->
                                                  FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___3 ->
                                                       Prims.strcat uu___1
                                                         uu___2)))) uu___1)))
                              (fun uu___1 ->
                                 FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___2 -> paren uu___1))))
                        (fun uu___1 ->
                           FStar_Tactics_Effect.lift_div_tac
                             (fun uu___2 -> Prims.strcat "Tv_Refine " uu___1))))
            | FStar_Reflection_Data.Tv_Const c ->
                Obj.magic (Obj.repr (const_to_ast_string c))
            | FStar_Reflection_Data.Tv_Uvar (i, uu___1) ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___2 ->
                           Prims.strcat "Tv_Uvar " (Prims.string_of_int i))))
            | FStar_Reflection_Data.Tv_Let (recf, uu___1, x, e1, e2) ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.tac_bind
                        (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                           (Prims.of_int (56)) (Prims.of_int (23))
                           (Prims.of_int (59)) (Prims.of_int (52)))
                        (FStar_Range.mk_range "prims.fst" (Prims.of_int (606))
                           (Prims.of_int (19)) (Prims.of_int (606))
                           (Prims.of_int (31)))
                        (Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                                 (Prims.of_int (56)) (Prims.of_int (29))
                                 (Prims.of_int (59)) (Prims.of_int (52)))
                              (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                                 (Prims.of_int (56)) (Prims.of_int (23))
                                 (Prims.of_int (59)) (Prims.of_int (52)))
                              (Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                                       (Prims.of_int (56))
                                       (Prims.of_int (52))
                                       (Prims.of_int (59))
                                       (Prims.of_int (51)))
                                    (FStar_Range.mk_range "prims.fst"
                                       (Prims.of_int (606))
                                       (Prims.of_int (19))
                                       (Prims.of_int (606))
                                       (Prims.of_int (31)))
                                    (Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Range.mk_range
                                             "FStar.Tactics.Print.fst"
                                             (Prims.of_int (57))
                                             (Prims.of_int (30))
                                             (Prims.of_int (59))
                                             (Prims.of_int (51)))
                                          (FStar_Range.mk_range "prims.fst"
                                             (Prims.of_int (606))
                                             (Prims.of_int (19))
                                             (Prims.of_int (606))
                                             (Prims.of_int (31)))
                                          (Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Range.mk_range
                                                   "FStar.Tactics.Print.fst"
                                                   (Prims.of_int (57))
                                                   (Prims.of_int (30))
                                                   (Prims.of_int (57))
                                                   (Prims.of_int (44)))
                                                (FStar_Range.mk_range
                                                   "FStar.Tactics.Print.fst"
                                                   (Prims.of_int (57))
                                                   (Prims.of_int (30))
                                                   (Prims.of_int (59))
                                                   (Prims.of_int (51)))
                                                (Obj.magic (bv_to_string x))
                                                (fun uu___2 ->
                                                   (fun uu___2 ->
                                                      Obj.magic
                                                        (FStar_Tactics_Effect.tac_bind
                                                           (FStar_Range.mk_range
                                                              "FStar.Tactics.Print.fst"
                                                              (Prims.of_int (57))
                                                              (Prims.of_int (47))
                                                              (Prims.of_int (59))
                                                              (Prims.of_int (51)))
                                                           (FStar_Range.mk_range
                                                              "prims.fst"
                                                              (Prims.of_int (606))
                                                              (Prims.of_int (19))
                                                              (Prims.of_int (606))
                                                              (Prims.of_int (31)))
                                                           (Obj.magic
                                                              (FStar_Tactics_Effect.tac_bind
                                                                 (FStar_Range.mk_range
                                                                    "FStar.Tactics.Print.fst"
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (51)))
                                                                 (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (31)))
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Print.fst"
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (51)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Print.fst"
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (51)))
                                                                    (Obj.magic
                                                                    (term_to_ast_string
                                                                    e1))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Print.fst"
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (51)))
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Print.fst"
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (51)))
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (term_to_ast_string
                                                                    e2))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Prims.strcat
                                                                    ", "
                                                                    uu___4))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Prims.strcat
                                                                    uu___3
                                                                    uu___4))))
                                                                    uu___3)))
                                                                 (fun uu___3
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Prims.strcat
                                                                    ", "
                                                                    uu___3))))
                                                           (fun uu___3 ->
                                                              FStar_Tactics_Effect.lift_div_tac
                                                                (fun uu___4
                                                                   ->
                                                                   Prims.strcat
                                                                    uu___2
                                                                    uu___3))))
                                                     uu___2)))
                                          (fun uu___2 ->
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___3 ->
                                                  Prims.strcat ", " uu___2))))
                                    (fun uu___2 ->
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___3 ->
                                            Prims.strcat
                                              (Prims.string_of_bool recf)
                                              uu___2))))
                              (fun uu___2 ->
                                 FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___3 -> paren uu___2))))
                        (fun uu___2 ->
                           FStar_Tactics_Effect.lift_div_tac
                             (fun uu___3 -> Prims.strcat "Tv_Let " uu___2))))
            | FStar_Reflection_Data.Tv_Match (e, ret_opt, brs) ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.tac_bind
                        (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                           (Prims.of_int (62)) (Prims.of_int (6))
                           (Prims.of_int (67)) (Prims.of_int (35)))
                        (FStar_Range.mk_range "prims.fst" (Prims.of_int (606))
                           (Prims.of_int (19)) (Prims.of_int (606))
                           (Prims.of_int (31)))
                        (Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                                 (Prims.of_int (62)) (Prims.of_int (12))
                                 (Prims.of_int (67)) (Prims.of_int (35)))
                              (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                                 (Prims.of_int (62)) (Prims.of_int (6))
                                 (Prims.of_int (67)) (Prims.of_int (35)))
                              (Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                                       (Prims.of_int (63)) (Prims.of_int (8))
                                       (Prims.of_int (63))
                                       (Prims.of_int (28)))
                                    (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                                       (Prims.of_int (62))
                                       (Prims.of_int (12))
                                       (Prims.of_int (67))
                                       (Prims.of_int (35)))
                                    (Obj.magic (term_to_ast_string e))
                                    (fun uu___1 ->
                                       (fun uu___1 ->
                                          Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Range.mk_range
                                                  "FStar.Tactics.Print.fst"
                                                  (Prims.of_int (64))
                                                  (Prims.of_int (8))
                                                  (Prims.of_int (67))
                                                  (Prims.of_int (34)))
                                               (FStar_Range.mk_range "prims.fst"
                                                  (Prims.of_int (606))
                                                  (Prims.of_int (19))
                                                  (Prims.of_int (606))
                                                  (Prims.of_int (31)))
                                               (Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Range.mk_range
                                                        "FStar.Tactics.Print.fst"
                                                        (Prims.of_int (65))
                                                        (Prims.of_int (8))
                                                        (Prims.of_int (67))
                                                        (Prims.of_int (34)))
                                                     (FStar_Range.mk_range
                                                        "prims.fst"
                                                        (Prims.of_int (606))
                                                        (Prims.of_int (19))
                                                        (Prims.of_int (606))
                                                        (Prims.of_int (31)))
                                                     (Obj.magic
                                                        (FStar_Tactics_Effect.tac_bind
                                                           (FStar_Range.mk_range
                                                              "FStar.Tactics.Print.fst"
                                                              (Prims.of_int (65))
                                                              (Prims.of_int (8))
                                                              (Prims.of_int (65))
                                                              (Prims.of_int (39)))
                                                           (FStar_Range.mk_range
                                                              "FStar.Tactics.Print.fst"
                                                              (Prims.of_int (65))
                                                              (Prims.of_int (8))
                                                              (Prims.of_int (67))
                                                              (Prims.of_int (34)))
                                                           (Obj.magic
                                                              (match_returns_to_string
                                                                 ret_opt))
                                                           (fun uu___2 ->
                                                              (fun uu___2 ->
                                                                 Obj.magic
                                                                   (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Print.fst"
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (34)))
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Print.fst"
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (34)))
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (branches_to_ast_string
                                                                    brs))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Prims.strcat
                                                                    ", "
                                                                    uu___3))))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Prims.strcat
                                                                    uu___2
                                                                    uu___3))))
                                                                uu___2)))
                                                     (fun uu___2 ->
                                                        FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___3 ->
                                                             Prims.strcat
                                                               ", " uu___2))))
                                               (fun uu___2 ->
                                                  FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___3 ->
                                                       Prims.strcat uu___1
                                                         uu___2)))) uu___1)))
                              (fun uu___1 ->
                                 FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___2 -> paren uu___1))))
                        (fun uu___1 ->
                           FStar_Tactics_Effect.lift_div_tac
                             (fun uu___2 -> Prims.strcat "Tv_Match " uu___1))))
            | FStar_Reflection_Data.Tv_AscribedT (e, t1, uu___1, use_eq) ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.tac_bind
                        (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                           (Prims.of_int (68)) (Prims.of_int (51))
                           (Prims.of_int (68)) (Prims.of_int (140)))
                        (FStar_Range.mk_range "prims.fst" (Prims.of_int (606))
                           (Prims.of_int (19)) (Prims.of_int (606))
                           (Prims.of_int (31)))
                        (Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                                 (Prims.of_int (68)) (Prims.of_int (57))
                                 (Prims.of_int (68)) (Prims.of_int (140)))
                              (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                                 (Prims.of_int (68)) (Prims.of_int (51))
                                 (Prims.of_int (68)) (Prims.of_int (140)))
                              (Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                                       (Prims.of_int (68))
                                       (Prims.of_int (58))
                                       (Prims.of_int (68))
                                       (Prims.of_int (78)))
                                    (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                                       (Prims.of_int (68))
                                       (Prims.of_int (57))
                                       (Prims.of_int (68))
                                       (Prims.of_int (140)))
                                    (Obj.magic (term_to_ast_string e))
                                    (fun uu___2 ->
                                       (fun uu___2 ->
                                          Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Range.mk_range
                                                  "FStar.Tactics.Print.fst"
                                                  (Prims.of_int (68))
                                                  (Prims.of_int (81))
                                                  (Prims.of_int (68))
                                                  (Prims.of_int (139)))
                                               (FStar_Range.mk_range "prims.fst"
                                                  (Prims.of_int (606))
                                                  (Prims.of_int (19))
                                                  (Prims.of_int (606))
                                                  (Prims.of_int (31)))
                                               (Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Range.mk_range
                                                        "FStar.Tactics.Print.fst"
                                                        (Prims.of_int (68))
                                                        (Prims.of_int (88))
                                                        (Prims.of_int (68))
                                                        (Prims.of_int (139)))
                                                     (FStar_Range.mk_range
                                                        "prims.fst"
                                                        (Prims.of_int (606))
                                                        (Prims.of_int (19))
                                                        (Prims.of_int (606))
                                                        (Prims.of_int (31)))
                                                     (Obj.magic
                                                        (FStar_Tactics_Effect.tac_bind
                                                           (FStar_Range.mk_range
                                                              "FStar.Tactics.Print.fst"
                                                              (Prims.of_int (68))
                                                              (Prims.of_int (88))
                                                              (Prims.of_int (68))
                                                              (Prims.of_int (108)))
                                                           (FStar_Range.mk_range
                                                              "prims.fst"
                                                              (Prims.of_int (606))
                                                              (Prims.of_int (19))
                                                              (Prims.of_int (606))
                                                              (Prims.of_int (31)))
                                                           (Obj.magic
                                                              (term_to_ast_string
                                                                 t1))
                                                           (fun uu___3 ->
                                                              FStar_Tactics_Effect.lift_div_tac
                                                                (fun uu___4
                                                                   ->
                                                                   Prims.strcat
                                                                    uu___3
                                                                    (Prims.strcat
                                                                    ", "
                                                                    (Prims.string_of_bool
                                                                    use_eq))))))
                                                     (fun uu___3 ->
                                                        FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___4 ->
                                                             Prims.strcat
                                                               ", " uu___3))))
                                               (fun uu___3 ->
                                                  FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___4 ->
                                                       Prims.strcat uu___2
                                                         uu___3)))) uu___2)))
                              (fun uu___2 ->
                                 FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___3 -> paren uu___2))))
                        (fun uu___2 ->
                           FStar_Tactics_Effect.lift_div_tac
                             (fun uu___3 ->
                                Prims.strcat "Tv_AscribedT " uu___2))))
            | FStar_Reflection_Data.Tv_AscribedC (e, c, uu___1, use_eq) ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.tac_bind
                        (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                           (Prims.of_int (69)) (Prims.of_int (51))
                           (Prims.of_int (69)) (Prims.of_int (140)))
                        (FStar_Range.mk_range "prims.fst" (Prims.of_int (606))
                           (Prims.of_int (19)) (Prims.of_int (606))
                           (Prims.of_int (31)))
                        (Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                                 (Prims.of_int (69)) (Prims.of_int (57))
                                 (Prims.of_int (69)) (Prims.of_int (140)))
                              (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                                 (Prims.of_int (69)) (Prims.of_int (51))
                                 (Prims.of_int (69)) (Prims.of_int (140)))
                              (Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                                       (Prims.of_int (69))
                                       (Prims.of_int (58))
                                       (Prims.of_int (69))
                                       (Prims.of_int (78)))
                                    (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                                       (Prims.of_int (69))
                                       (Prims.of_int (57))
                                       (Prims.of_int (69))
                                       (Prims.of_int (140)))
                                    (Obj.magic (term_to_ast_string e))
                                    (fun uu___2 ->
                                       (fun uu___2 ->
                                          Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Range.mk_range
                                                  "FStar.Tactics.Print.fst"
                                                  (Prims.of_int (69))
                                                  (Prims.of_int (81))
                                                  (Prims.of_int (69))
                                                  (Prims.of_int (139)))
                                               (FStar_Range.mk_range "prims.fst"
                                                  (Prims.of_int (606))
                                                  (Prims.of_int (19))
                                                  (Prims.of_int (606))
                                                  (Prims.of_int (31)))
                                               (Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Range.mk_range
                                                        "FStar.Tactics.Print.fst"
                                                        (Prims.of_int (69))
                                                        (Prims.of_int (88))
                                                        (Prims.of_int (69))
                                                        (Prims.of_int (139)))
                                                     (FStar_Range.mk_range
                                                        "prims.fst"
                                                        (Prims.of_int (606))
                                                        (Prims.of_int (19))
                                                        (Prims.of_int (606))
                                                        (Prims.of_int (31)))
                                                     (Obj.magic
                                                        (FStar_Tactics_Effect.tac_bind
                                                           (FStar_Range.mk_range
                                                              "FStar.Tactics.Print.fst"
                                                              (Prims.of_int (69))
                                                              (Prims.of_int (88))
                                                              (Prims.of_int (69))
                                                              (Prims.of_int (108)))
                                                           (FStar_Range.mk_range
                                                              "prims.fst"
                                                              (Prims.of_int (606))
                                                              (Prims.of_int (19))
                                                              (Prims.of_int (606))
                                                              (Prims.of_int (31)))
                                                           (Obj.magic
                                                              (comp_to_ast_string
                                                                 c))
                                                           (fun uu___3 ->
                                                              FStar_Tactics_Effect.lift_div_tac
                                                                (fun uu___4
                                                                   ->
                                                                   Prims.strcat
                                                                    uu___3
                                                                    (Prims.strcat
                                                                    ", "
                                                                    (Prims.string_of_bool
                                                                    use_eq))))))
                                                     (fun uu___3 ->
                                                        FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___4 ->
                                                             Prims.strcat
                                                               ", " uu___3))))
                                               (fun uu___3 ->
                                                  FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___4 ->
                                                       Prims.strcat uu___2
                                                         uu___3)))) uu___2)))
                              (fun uu___2 ->
                                 FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___3 -> paren uu___2))))
                        (fun uu___2 ->
                           FStar_Tactics_Effect.lift_div_tac
                             (fun uu___3 ->
                                Prims.strcat "Tv_AscribedC " uu___2))))
            | FStar_Reflection_Data.Tv_Unknown ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> "_"))))
           uu___)
and (match_returns_to_string :
  FStar_Reflection_Types.match_returns_ascription
    FStar_Pervasives_Native.option ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun ret_opt ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Range.mk_range "FStar.Tactics.Print.fst" (Prims.of_int (74))
         (Prims.of_int (4)) (Prims.of_int (76)) (Prims.of_int (51)))
      (FStar_Range.mk_range "FStar.Tactics.Print.fst" (Prims.of_int (77))
         (Prims.of_int (2)) (Prims.of_int (84)) (Prims.of_int (78)))
      (FStar_Tactics_Effect.lift_div_tac
         (fun uu___1 ->
            fun uu___ ->
              (fun uu___ ->
                 fun tacopt ->
                   match tacopt with
                   | FStar_Pervasives_Native.None ->
                       Obj.magic
                         (Obj.repr
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___1 -> "")))
                   | FStar_Pervasives_Native.Some tac ->
                       Obj.magic
                         (Obj.repr
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                                  (Prims.of_int (76)) (Prims.of_int (27))
                                  (Prims.of_int (76)) (Prims.of_int (51)))
                               (FStar_Range.mk_range "prims.fst"
                                  (Prims.of_int (606)) (Prims.of_int (19))
                                  (Prims.of_int (606)) (Prims.of_int (31)))
                               (Obj.magic (term_to_ast_string tac))
                               (fun uu___1 ->
                                  FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___2 -> Prims.strcat " by " uu___1)))))
                uu___1 uu___))
      (fun uu___ ->
         (fun tacopt_to_string ->
            match ret_opt with
            | FStar_Pervasives_Native.None ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> "")))
            | FStar_Pervasives_Native.Some (b, asc) ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.tac_bind
                        (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                           (Prims.of_int (80)) (Prims.of_int (4))
                           (Prims.of_int (80)) (Prims.of_int (30)))
                        (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                           (Prims.of_int (80)) (Prims.of_int (4))
                           (Prims.of_int (84)) (Prims.of_int (78)))
                        (Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                                 (Prims.of_int (80)) (Prims.of_int (5))
                                 (Prims.of_int (80)) (Prims.of_int (23)))
                              (FStar_Range.mk_range "prims.fst"
                                 (Prims.of_int (606)) (Prims.of_int (19))
                                 (Prims.of_int (606)) (Prims.of_int (31)))
                              (Obj.magic
                                 (FStar_Tactics_Derived.binder_to_string b))
                              (fun uu___ ->
                                 FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___1 -> Prims.strcat uu___ " "))))
                        (fun uu___ ->
                           (fun uu___ ->
                              Obj.magic
                                (FStar_Tactics_Effect.tac_bind
                                   (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                                      (Prims.of_int (82)) (Prims.of_int (4))
                                      (Prims.of_int (84)) (Prims.of_int (78)))
                                   (FStar_Range.mk_range "prims.fst"
                                      (Prims.of_int (606))
                                      (Prims.of_int (19))
                                      (Prims.of_int (606))
                                      (Prims.of_int (31)))
                                   (match asc with
                                    | (FStar_Pervasives.Inl t, tacopt,
                                       uu___1) ->
                                        Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.Print.fst"
                                                (Prims.of_int (83))
                                                (Prims.of_int (27))
                                                (Prims.of_int (83))
                                                (Prims.of_int (49)))
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.Print.fst"
                                                (Prims.of_int (83))
                                                (Prims.of_int (27))
                                                (Prims.of_int (83))
                                                (Prims.of_int (77)))
                                             (Obj.magic
                                                (term_to_ast_string t))
                                             (fun uu___2 ->
                                                (fun uu___2 ->
                                                   Obj.magic
                                                     (FStar_Tactics_Effect.tac_bind
                                                        (FStar_Range.mk_range
                                                           "FStar.Tactics.Print.fst"
                                                           (Prims.of_int (83))
                                                           (Prims.of_int (52))
                                                           (Prims.of_int (83))
                                                           (Prims.of_int (77)))
                                                        (FStar_Range.mk_range
                                                           "prims.fst"
                                                           (Prims.of_int (606))
                                                           (Prims.of_int (19))
                                                           (Prims.of_int (606))
                                                           (Prims.of_int (31)))
                                                        (Obj.magic
                                                           (tacopt_to_string
                                                              tacopt))
                                                        (fun uu___3 ->
                                                           FStar_Tactics_Effect.lift_div_tac
                                                             (fun uu___4 ->
                                                                Prims.strcat
                                                                  uu___2
                                                                  uu___3))))
                                                  uu___2))
                                    | (FStar_Pervasives.Inr c, tacopt,
                                       uu___1) ->
                                        Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.Print.fst"
                                                (Prims.of_int (84))
                                                (Prims.of_int (27))
                                                (Prims.of_int (84))
                                                (Prims.of_int (49)))
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.Print.fst"
                                                (Prims.of_int (84))
                                                (Prims.of_int (27))
                                                (Prims.of_int (84))
                                                (Prims.of_int (77)))
                                             (Obj.magic
                                                (comp_to_ast_string c))
                                             (fun uu___2 ->
                                                (fun uu___2 ->
                                                   Obj.magic
                                                     (FStar_Tactics_Effect.tac_bind
                                                        (FStar_Range.mk_range
                                                           "FStar.Tactics.Print.fst"
                                                           (Prims.of_int (84))
                                                           (Prims.of_int (52))
                                                           (Prims.of_int (84))
                                                           (Prims.of_int (77)))
                                                        (FStar_Range.mk_range
                                                           "prims.fst"
                                                           (Prims.of_int (606))
                                                           (Prims.of_int (19))
                                                           (Prims.of_int (606))
                                                           (Prims.of_int (31)))
                                                        (Obj.magic
                                                           (tacopt_to_string
                                                              tacopt))
                                                        (fun uu___3 ->
                                                           FStar_Tactics_Effect.lift_div_tac
                                                             (fun uu___4 ->
                                                                Prims.strcat
                                                                  uu___2
                                                                  uu___3))))
                                                  uu___2)))
                                   (fun uu___1 ->
                                      FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___2 ->
                                           Prims.strcat uu___ uu___1))))
                             uu___)))) uu___)
and (branches_to_ast_string :
  FStar_Reflection_Data.branch Prims.list ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  = fun brs -> print_list branch_to_ast_string brs
and (branch_to_ast_string :
  FStar_Reflection_Data.branch ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun b ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Range.mk_range "FStar.Tactics.Print.fst" (Prims.of_int (90))
         (Prims.of_int (13)) (Prims.of_int (90)) (Prims.of_int (14)))
      (FStar_Range.mk_range "FStar.Tactics.Print.fst" (Prims.of_int (90))
         (Prims.of_int (2)) (Prims.of_int (91)) (Prims.of_int (41)))
      (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> b))
      (fun uu___ ->
         (fun uu___ ->
            match uu___ with
            | (p, e) ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                        (Prims.of_int (91)) (Prims.of_int (8))
                        (Prims.of_int (91)) (Prims.of_int (41)))
                     (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                        (Prims.of_int (91)) (Prims.of_int (2))
                        (Prims.of_int (91)) (Prims.of_int (41)))
                     (Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                              (Prims.of_int (91)) (Prims.of_int (20))
                              (Prims.of_int (91)) (Prims.of_int (40)))
                           (FStar_Range.mk_range "prims.fst" (Prims.of_int (606))
                              (Prims.of_int (19)) (Prims.of_int (606))
                              (Prims.of_int (31)))
                           (Obj.magic (term_to_ast_string e))
                           (fun uu___1 ->
                              FStar_Tactics_Effect.lift_div_tac
                                (fun uu___2 -> Prims.strcat "_pat, " uu___1))))
                     (fun uu___1 ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___2 -> paren uu___1)))) uu___)
and (comp_to_ast_string :
  FStar_Reflection_Types.comp ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun c ->
    match FStar_Reflection_Builtins.inspect_comp c with
    | FStar_Reflection_Data.C_Total t ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Range.mk_range "FStar.Tactics.Print.fst" (Prims.of_int (95))
             (Prims.of_int (26)) (Prims.of_int (95)) (Prims.of_int (46)))
          (FStar_Range.mk_range "prims.fst" (Prims.of_int (606))
             (Prims.of_int (19)) (Prims.of_int (606)) (Prims.of_int (31)))
          (Obj.magic (term_to_ast_string t))
          (fun uu___ ->
             FStar_Tactics_Effect.lift_div_tac
               (fun uu___1 -> Prims.strcat "Tot " uu___))
    | FStar_Reflection_Data.C_GTotal t ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Range.mk_range "FStar.Tactics.Print.fst" (Prims.of_int (96))
             (Prims.of_int (28)) (Prims.of_int (96)) (Prims.of_int (48)))
          (FStar_Range.mk_range "prims.fst" (Prims.of_int (606))
             (Prims.of_int (19)) (Prims.of_int (606)) (Prims.of_int (31)))
          (Obj.magic (term_to_ast_string t))
          (fun uu___ ->
             FStar_Tactics_Effect.lift_div_tac
               (fun uu___1 -> Prims.strcat "GTot " uu___))
    | FStar_Reflection_Data.C_Lemma (pre, post, uu___) ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Range.mk_range "FStar.Tactics.Print.fst" (Prims.of_int (97))
             (Prims.of_int (37)) (Prims.of_int (97)) (Prims.of_int (91)))
          (FStar_Range.mk_range "prims.fst" (Prims.of_int (606))
             (Prims.of_int (19)) (Prims.of_int (606)) (Prims.of_int (31)))
          (Obj.magic
             (FStar_Tactics_Effect.tac_bind
                (FStar_Range.mk_range "FStar.Tactics.Print.fst" (Prims.of_int (97))
                   (Prims.of_int (37)) (Prims.of_int (97))
                   (Prims.of_int (59)))
                (FStar_Range.mk_range "FStar.Tactics.Print.fst" (Prims.of_int (97))
                   (Prims.of_int (37)) (Prims.of_int (97))
                   (Prims.of_int (91))) (Obj.magic (term_to_ast_string pre))
                (fun uu___1 ->
                   (fun uu___1 ->
                      Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                              (Prims.of_int (97)) (Prims.of_int (62))
                              (Prims.of_int (97)) (Prims.of_int (91)))
                           (FStar_Range.mk_range "prims.fst" (Prims.of_int (606))
                              (Prims.of_int (19)) (Prims.of_int (606))
                              (Prims.of_int (31)))
                           (Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                                    (Prims.of_int (97)) (Prims.of_int (68))
                                    (Prims.of_int (97)) (Prims.of_int (91)))
                                 (FStar_Range.mk_range "prims.fst"
                                    (Prims.of_int (606)) (Prims.of_int (19))
                                    (Prims.of_int (606)) (Prims.of_int (31)))
                                 (Obj.magic (term_to_ast_string post))
                                 (fun uu___2 ->
                                    FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___3 -> Prims.strcat " " uu___2))))
                           (fun uu___2 ->
                              FStar_Tactics_Effect.lift_div_tac
                                (fun uu___3 -> Prims.strcat uu___1 uu___2))))
                     uu___1)))
          (fun uu___1 ->
             FStar_Tactics_Effect.lift_div_tac
               (fun uu___2 -> Prims.strcat "Lemma " uu___1))
    | FStar_Reflection_Data.C_Eff (us, eff, res, uu___, uu___1) ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Range.mk_range "FStar.Tactics.Print.fst" (Prims.of_int (99))
             (Prims.of_int (15)) (Prims.of_int (99)) (Prims.of_int (111)))
          (FStar_Range.mk_range "prims.fst" (Prims.of_int (606))
             (Prims.of_int (19)) (Prims.of_int (606)) (Prims.of_int (31)))
          (Obj.magic
             (FStar_Tactics_Effect.tac_bind
                (FStar_Range.mk_range "FStar.Tactics.Print.fst" (Prims.of_int (99))
                   (Prims.of_int (21)) (Prims.of_int (99))
                   (Prims.of_int (111)))
                (FStar_Range.mk_range "prims.fst" (Prims.of_int (606))
                   (Prims.of_int (19)) (Prims.of_int (606))
                   (Prims.of_int (31)))
                (Obj.magic
                   (FStar_Tactics_Effect.tac_bind
                      (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                         (Prims.of_int (99)) (Prims.of_int (21))
                         (Prims.of_int (99)) (Prims.of_int (47)))
                      (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                         (Prims.of_int (99)) (Prims.of_int (21))
                         (Prims.of_int (99)) (Prims.of_int (111)))
                      (Obj.magic (universes_to_ast_string us))
                      (fun uu___2 ->
                         (fun uu___2 ->
                            Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                                    (Prims.of_int (99)) (Prims.of_int (50))
                                    (Prims.of_int (99)) (Prims.of_int (111)))
                                 (FStar_Range.mk_range "prims.fst"
                                    (Prims.of_int (606)) (Prims.of_int (19))
                                    (Prims.of_int (606)) (Prims.of_int (31)))
                                 (Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Range.mk_range
                                          "FStar.Tactics.Print.fst"
                                          (Prims.of_int (99))
                                          (Prims.of_int (57))
                                          (Prims.of_int (99))
                                          (Prims.of_int (111)))
                                       (FStar_Range.mk_range "prims.fst"
                                          (Prims.of_int (606))
                                          (Prims.of_int (19))
                                          (Prims.of_int (606))
                                          (Prims.of_int (31)))
                                       (Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.Print.fst"
                                                (Prims.of_int (99))
                                                (Prims.of_int (63))
                                                (Prims.of_int (99))
                                                (Prims.of_int (111)))
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.Print.fst"
                                                (Prims.of_int (99))
                                                (Prims.of_int (57))
                                                (Prims.of_int (99))
                                                (Prims.of_int (111)))
                                             (Obj.magic
                                                (FStar_Tactics_Effect.tac_bind
                                                   (FStar_Range.mk_range
                                                      "FStar.Tactics.Print.fst"
                                                      (Prims.of_int (99))
                                                      (Prims.of_int (81))
                                                      (Prims.of_int (99))
                                                      (Prims.of_int (110)))
                                                   (FStar_Range.mk_range
                                                      "prims.fst"
                                                      (Prims.of_int (606))
                                                      (Prims.of_int (19))
                                                      (Prims.of_int (606))
                                                      (Prims.of_int (31)))
                                                   (Obj.magic
                                                      (FStar_Tactics_Effect.tac_bind
                                                         (FStar_Range.mk_range
                                                            "FStar.Tactics.Print.fst"
                                                            (Prims.of_int (99))
                                                            (Prims.of_int (88))
                                                            (Prims.of_int (99))
                                                            (Prims.of_int (110)))
                                                         (FStar_Range.mk_range
                                                            "prims.fst"
                                                            (Prims.of_int (606))
                                                            (Prims.of_int (19))
                                                            (Prims.of_int (606))
                                                            (Prims.of_int (31)))
                                                         (Obj.magic
                                                            (term_to_ast_string
                                                               res))
                                                         (fun uu___3 ->
                                                            FStar_Tactics_Effect.lift_div_tac
                                                              (fun uu___4 ->
                                                                 Prims.strcat
                                                                   ", "
                                                                   uu___3))))
                                                   (fun uu___3 ->
                                                      FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___4 ->
                                                           Prims.strcat
                                                             (FStar_Reflection_Builtins.implode_qn
                                                                eff) uu___3))))
                                             (fun uu___3 ->
                                                FStar_Tactics_Effect.lift_div_tac
                                                  (fun uu___4 -> paren uu___3))))
                                       (fun uu___3 ->
                                          FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___4 ->
                                               Prims.strcat "> " uu___3))))
                                 (fun uu___3 ->
                                    FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___4 ->
                                         Prims.strcat uu___2 uu___3))))
                           uu___2)))
                (fun uu___2 ->
                   FStar_Tactics_Effect.lift_div_tac
                     (fun uu___3 -> Prims.strcat "<" uu___2))))
          (fun uu___2 ->
             FStar_Tactics_Effect.lift_div_tac
               (fun uu___3 -> Prims.strcat "Effect" uu___2))
and (const_to_ast_string :
  FStar_Reflection_Data.vconst ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    (fun c ->
       Obj.magic
         (FStar_Tactics_Effect.lift_div_tac
            (fun uu___ ->
               match c with
               | FStar_Reflection_Data.C_Unit -> "C_Unit"
               | FStar_Reflection_Data.C_Int i ->
                   Prims.strcat "C_Int " (Prims.string_of_int i)
               | FStar_Reflection_Data.C_True -> "C_True"
               | FStar_Reflection_Data.C_False -> "C_False"
               | FStar_Reflection_Data.C_String s ->
                   Prims.strcat "C_String " s
               | FStar_Reflection_Data.C_Range uu___1 -> "C_Range _"
               | FStar_Reflection_Data.C_Reify -> "C_Reify"
               | FStar_Reflection_Data.C_Reflect name ->
                   Prims.strcat "C_Reflect "
                     (FStar_Reflection_Builtins.implode_qn name)))) uu___