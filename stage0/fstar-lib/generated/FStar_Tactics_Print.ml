open Prims
let (namedv_to_string :
  FStar_Tactics_NamedView.namedv ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun x ->
    let uu___ =
      FStarC_Tactics_Unseal.unseal x.FStarC_Reflection_V2_Data.ppname in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.Print.fst"
               (Prims.of_int (10)) (Prims.of_int (2)) (Prims.of_int (10))
               (Prims.of_int (17)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Prims.fst" (Prims.of_int (611))
               (Prims.of_int (19)) (Prims.of_int (611)) (Prims.of_int (31)))))
      (Obj.magic uu___)
      (fun uu___1 ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___2 ->
              Prims.strcat uu___1
                (Prims.strcat "#"
                   (Prims.string_of_int x.FStarC_Reflection_V2_Data.uniq))))
let _ =
  FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.Print.namedv_to_string" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.Print.namedv_to_string (plugin)"
               (FStarC_Tactics_Native.from_tactic_1 namedv_to_string)
               FStarC_Reflection_V2_Embeddings.e_namedv_view
               FStarC_Syntax_Embeddings.e_string psc ncb us args)
let (paren : Prims.string -> Prims.string) =
  fun s -> Prims.strcat "(" (Prims.strcat s ")")
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
                    (let uu___ = f x in
                     FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                                (Prims.of_int (21)) (Prims.of_int (13))
                                (Prims.of_int (21)) (Prims.of_int (16)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                                (Prims.of_int (21)) (Prims.of_int (13))
                                (Prims.of_int (21)) (Prims.of_int (45)))))
                       (Obj.magic uu___)
                       (fun uu___1 ->
                          (fun uu___1 ->
                             let uu___2 =
                               let uu___3 = print_list_aux f xs1 in
                               FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "FStar.Tactics.Print.fst"
                                          (Prims.of_int (21))
                                          (Prims.of_int (26))
                                          (Prims.of_int (21))
                                          (Prims.of_int (45)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range "Prims.fst"
                                          (Prims.of_int (611))
                                          (Prims.of_int (19))
                                          (Prims.of_int (611))
                                          (Prims.of_int (31)))))
                                 (Obj.magic uu___3)
                                 (fun uu___4 ->
                                    FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___5 -> Prims.strcat "; " uu___4)) in
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "FStar.Tactics.Print.fst"
                                           (Prims.of_int (21))
                                           (Prims.of_int (19))
                                           (Prims.of_int (21))
                                           (Prims.of_int (45)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range "Prims.fst"
                                           (Prims.of_int (611))
                                           (Prims.of_int (19))
                                           (Prims.of_int (611))
                                           (Prims.of_int (31)))))
                                  (Obj.magic uu___2)
                                  (fun uu___3 ->
                                     FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___4 ->
                                          Prims.strcat uu___1 uu___3))))
                            uu___1)))) uu___1 uu___
let print_list :
  'a .
    ('a -> (Prims.string, unit) FStar_Tactics_Effect.tac_repr) ->
      'a Prims.list -> (Prims.string, unit) FStar_Tactics_Effect.tac_repr
  =
  fun f ->
    fun l ->
      let uu___ =
        let uu___1 = print_list_aux f l in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                   (Prims.of_int (25)) (Prims.of_int (9)) (Prims.of_int (25))
                   (Prims.of_int (27)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Prims.fst" (Prims.of_int (611))
                   (Prims.of_int (19)) (Prims.of_int (611))
                   (Prims.of_int (31))))) (Obj.magic uu___1)
          (fun uu___2 ->
             FStar_Tactics_Effect.lift_div_tac
               (fun uu___3 -> Prims.strcat uu___2 "]")) in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                 (Prims.of_int (25)) (Prims.of_int (9)) (Prims.of_int (25))
                 (Prims.of_int (33)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Prims.fst" (Prims.of_int (611))
                 (Prims.of_int (19)) (Prims.of_int (611)) (Prims.of_int (31)))))
        (Obj.magic uu___)
        (fun uu___1 ->
           FStar_Tactics_Effect.lift_div_tac
             (fun uu___2 -> Prims.strcat "[" uu___1))
let rec (universe_to_ast_string :
  FStar_Tactics_NamedView.universe ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    (fun u ->
       match FStar_Tactics_NamedView.inspect_universe u with
       | FStar_Tactics_NamedView.Uv_Zero ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> "Uv_Zero")))
       | FStar_Tactics_NamedView.Uv_Succ u1 ->
           Obj.magic
             (Obj.repr
                (let uu___ =
                   let uu___1 = universe_to_ast_string u1 in
                   FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                              (Prims.of_int (30)) (Prims.of_int (35))
                              (Prims.of_int (30)) (Prims.of_int (61)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                              (Prims.of_int (30)) (Prims.of_int (29))
                              (Prims.of_int (30)) (Prims.of_int (61)))))
                     (Obj.magic uu___1)
                     (fun uu___2 ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___3 -> paren uu___2)) in
                 FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                            (Prims.of_int (30)) (Prims.of_int (29))
                            (Prims.of_int (30)) (Prims.of_int (61)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Prims.fst"
                            (Prims.of_int (611)) (Prims.of_int (19))
                            (Prims.of_int (611)) (Prims.of_int (31)))))
                   (Obj.magic uu___)
                   (fun uu___1 ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___2 -> Prims.strcat "Uv_Succ" uu___1))))
       | FStar_Tactics_NamedView.Uv_Max us ->
           Obj.magic
             (Obj.repr
                (let uu___ = print_list universe_to_ast_string us in
                 FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                            (Prims.of_int (31)) (Prims.of_int (28))
                            (Prims.of_int (31)) (Prims.of_int (64)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Prims.fst"
                            (Prims.of_int (611)) (Prims.of_int (19))
                            (Prims.of_int (611)) (Prims.of_int (31)))))
                   (Obj.magic uu___)
                   (fun uu___1 ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___2 -> Prims.strcat "Uv_Max" uu___1))))
       | FStar_Tactics_NamedView.Uv_BVar n ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___ ->
                      Prims.strcat "Uv_BVar" (paren (Prims.string_of_int n)))))
       | FStar_Tactics_NamedView.Uv_Name i ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___ ->
                      Prims.strcat "Uv_Name"
                        (paren (FStar_Pervasives_Native.fst i)))))
       | FStar_Tactics_NamedView.Uv_Unif uu___ ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> "Uv_Unif")))
       | FStar_Tactics_NamedView.Uv_Unk ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> "Uv_Unk"))))
      uu___
let _ =
  FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.Print.universe_to_ast_string" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.Print.universe_to_ast_string (plugin)"
               (FStarC_Tactics_Native.from_tactic_1 universe_to_ast_string)
               FStarC_Reflection_V2_Embeddings.e_universe
               FStarC_Syntax_Embeddings.e_string psc ncb us args)
let (universes_to_ast_string :
  FStarC_Reflection_V2_Data.universes ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  = fun us -> print_list universe_to_ast_string us
let _ =
  FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.Print.universes_to_ast_string" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.Print.universes_to_ast_string (plugin)"
               (FStarC_Tactics_Native.from_tactic_1 universes_to_ast_string)
               (FStarC_Syntax_Embeddings.e_list
                  FStarC_Reflection_V2_Embeddings.e_universe)
               FStarC_Syntax_Embeddings.e_string psc ncb us args)
let rec (term_to_ast_string :
  FStar_Tactics_NamedView.term ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    let uu___ = FStar_Tactics_NamedView.inspect t in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.Print.fst"
               (Prims.of_int (41)) (Prims.of_int (8)) (Prims.of_int (41))
               (Prims.of_int (17)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.Print.fst"
               (Prims.of_int (41)) (Prims.of_int (2)) (Prims.of_int (70))
               (Prims.of_int (30))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun uu___1 ->
            match uu___1 with
            | FStar_Tactics_NamedView.Tv_Var bv ->
                Obj.magic
                  (Obj.repr
                     (let uu___2 = namedv_to_string bv in
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                                 (Prims.of_int (42)) (Prims.of_int (29))
                                 (Prims.of_int (42)) (Prims.of_int (48)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "Prims.fst"
                                 (Prims.of_int (611)) (Prims.of_int (19))
                                 (Prims.of_int (611)) (Prims.of_int (31)))))
                        (Obj.magic uu___2)
                        (fun uu___3 ->
                           FStar_Tactics_Effect.lift_div_tac
                             (fun uu___4 -> Prims.strcat "Tv_Var " uu___3))))
            | FStar_Tactics_NamedView.Tv_BVar bv ->
                Obj.magic
                  (Obj.repr
                     (let uu___2 = FStar_Tactics_V2_Derived.bv_to_string bv in
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                                 (Prims.of_int (43)) (Prims.of_int (31))
                                 (Prims.of_int (43)) (Prims.of_int (46)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "Prims.fst"
                                 (Prims.of_int (611)) (Prims.of_int (19))
                                 (Prims.of_int (611)) (Prims.of_int (31)))))
                        (Obj.magic uu___2)
                        (fun uu___3 ->
                           FStar_Tactics_Effect.lift_div_tac
                             (fun uu___4 -> Prims.strcat "Tv_BVar " uu___3))))
            | FStar_Tactics_NamedView.Tv_FVar fv ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___2 ->
                           Prims.strcat "Tv_FVar "
                             (FStar_Reflection_V2_Derived.fv_to_string fv))))
            | FStar_Tactics_NamedView.Tv_UInst (fv, us) ->
                Obj.magic
                  (Obj.repr
                     (let uu___2 =
                        let uu___3 =
                          let uu___4 =
                            let uu___5 = universes_to_ast_string us in
                            FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "FStar.Tactics.Print.fst"
                                       (Prims.of_int (46))
                                       (Prims.of_int (49))
                                       (Prims.of_int (46))
                                       (Prims.of_int (75)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range "Prims.fst"
                                       (Prims.of_int (611))
                                       (Prims.of_int (19))
                                       (Prims.of_int (611))
                                       (Prims.of_int (31)))))
                              (Obj.magic uu___5)
                              (fun uu___6 ->
                                 FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___7 -> Prims.strcat ", " uu___6)) in
                          FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.Print.fst"
                                     (Prims.of_int (46)) (Prims.of_int (42))
                                     (Prims.of_int (46)) (Prims.of_int (75)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range "Prims.fst"
                                     (Prims.of_int (611)) (Prims.of_int (19))
                                     (Prims.of_int (611)) (Prims.of_int (31)))))
                            (Obj.magic uu___4)
                            (fun uu___5 ->
                               FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___6 ->
                                    Prims.strcat
                                      (FStar_Reflection_V2_Derived.fv_to_string
                                         fv) uu___5)) in
                        FStar_Tactics_Effect.tac_bind
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "FStar.Tactics.Print.fst"
                                   (Prims.of_int (46)) (Prims.of_int (23))
                                   (Prims.of_int (46)) (Prims.of_int (76)))))
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "FStar.Tactics.Print.fst"
                                   (Prims.of_int (46)) (Prims.of_int (17))
                                   (Prims.of_int (46)) (Prims.of_int (76)))))
                          (Obj.magic uu___3)
                          (fun uu___4 ->
                             FStar_Tactics_Effect.lift_div_tac
                               (fun uu___5 -> paren uu___4)) in
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                                 (Prims.of_int (46)) (Prims.of_int (17))
                                 (Prims.of_int (46)) (Prims.of_int (76)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "Prims.fst"
                                 (Prims.of_int (611)) (Prims.of_int (19))
                                 (Prims.of_int (611)) (Prims.of_int (31)))))
                        (Obj.magic uu___2)
                        (fun uu___3 ->
                           FStar_Tactics_Effect.lift_div_tac
                             (fun uu___4 -> Prims.strcat "Tv_UInst" uu___3))))
            | FStar_Tactics_NamedView.Tv_App (hd, (a, uu___2)) ->
                Obj.magic
                  (Obj.repr
                     (let uu___3 =
                        let uu___4 =
                          let uu___5 = term_to_ast_string hd in
                          FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.Print.fst"
                                     (Prims.of_int (47)) (Prims.of_int (43))
                                     (Prims.of_int (47)) (Prims.of_int (64)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.Print.fst"
                                     (Prims.of_int (47)) (Prims.of_int (42))
                                     (Prims.of_int (47)) (Prims.of_int (95)))))
                            (Obj.magic uu___5)
                            (fun uu___6 ->
                               (fun uu___6 ->
                                  let uu___7 =
                                    let uu___8 = term_to_ast_string a in
                                    FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "FStar.Tactics.Print.fst"
                                               (Prims.of_int (47))
                                               (Prims.of_int (74))
                                               (Prims.of_int (47))
                                               (Prims.of_int (94)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range "Prims.fst"
                                               (Prims.of_int (611))
                                               (Prims.of_int (19))
                                               (Prims.of_int (611))
                                               (Prims.of_int (31)))))
                                      (Obj.magic uu___8)
                                      (fun uu___9 ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___10 ->
                                              Prims.strcat ", " uu___9)) in
                                  Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.Print.fst"
                                                (Prims.of_int (47))
                                                (Prims.of_int (67))
                                                (Prims.of_int (47))
                                                (Prims.of_int (94)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Prims.fst"
                                                (Prims.of_int (611))
                                                (Prims.of_int (19))
                                                (Prims.of_int (611))
                                                (Prims.of_int (31)))))
                                       (Obj.magic uu___7)
                                       (fun uu___8 ->
                                          FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___9 ->
                                               Prims.strcat uu___6 uu___8))))
                                 uu___6) in
                        FStar_Tactics_Effect.tac_bind
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "FStar.Tactics.Print.fst"
                                   (Prims.of_int (47)) (Prims.of_int (42))
                                   (Prims.of_int (47)) (Prims.of_int (95)))))
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "FStar.Tactics.Print.fst"
                                   (Prims.of_int (47)) (Prims.of_int (36))
                                   (Prims.of_int (47)) (Prims.of_int (95)))))
                          (Obj.magic uu___4)
                          (fun uu___5 ->
                             FStar_Tactics_Effect.lift_div_tac
                               (fun uu___6 -> paren uu___5)) in
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                                 (Prims.of_int (47)) (Prims.of_int (36))
                                 (Prims.of_int (47)) (Prims.of_int (95)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "Prims.fst"
                                 (Prims.of_int (611)) (Prims.of_int (19))
                                 (Prims.of_int (611)) (Prims.of_int (31)))))
                        (Obj.magic uu___3)
                        (fun uu___4 ->
                           FStar_Tactics_Effect.lift_div_tac
                             (fun uu___5 -> Prims.strcat "Tv_App " uu___4))))
            | FStar_Tactics_NamedView.Tv_Abs (x, e) ->
                Obj.magic
                  (Obj.repr
                     (let uu___2 =
                        let uu___3 =
                          let uu___4 =
                            FStar_Tactics_V2_Derived.binder_to_string x in
                          FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.Print.fst"
                                     (Prims.of_int (48)) (Prims.of_int (37))
                                     (Prims.of_int (48)) (Prims.of_int (55)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.Print.fst"
                                     (Prims.of_int (48)) (Prims.of_int (36))
                                     (Prims.of_int (48)) (Prims.of_int (86)))))
                            (Obj.magic uu___4)
                            (fun uu___5 ->
                               (fun uu___5 ->
                                  let uu___6 =
                                    let uu___7 = term_to_ast_string e in
                                    FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "FStar.Tactics.Print.fst"
                                               (Prims.of_int (48))
                                               (Prims.of_int (65))
                                               (Prims.of_int (48))
                                               (Prims.of_int (85)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range "Prims.fst"
                                               (Prims.of_int (611))
                                               (Prims.of_int (19))
                                               (Prims.of_int (611))
                                               (Prims.of_int (31)))))
                                      (Obj.magic uu___7)
                                      (fun uu___8 ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___9 ->
                                              Prims.strcat ", " uu___8)) in
                                  Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.Print.fst"
                                                (Prims.of_int (48))
                                                (Prims.of_int (58))
                                                (Prims.of_int (48))
                                                (Prims.of_int (85)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Prims.fst"
                                                (Prims.of_int (611))
                                                (Prims.of_int (19))
                                                (Prims.of_int (611))
                                                (Prims.of_int (31)))))
                                       (Obj.magic uu___6)
                                       (fun uu___7 ->
                                          FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___8 ->
                                               Prims.strcat uu___5 uu___7))))
                                 uu___5) in
                        FStar_Tactics_Effect.tac_bind
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "FStar.Tactics.Print.fst"
                                   (Prims.of_int (48)) (Prims.of_int (36))
                                   (Prims.of_int (48)) (Prims.of_int (86)))))
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "FStar.Tactics.Print.fst"
                                   (Prims.of_int (48)) (Prims.of_int (30))
                                   (Prims.of_int (48)) (Prims.of_int (86)))))
                          (Obj.magic uu___3)
                          (fun uu___4 ->
                             FStar_Tactics_Effect.lift_div_tac
                               (fun uu___5 -> paren uu___4)) in
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                                 (Prims.of_int (48)) (Prims.of_int (30))
                                 (Prims.of_int (48)) (Prims.of_int (86)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "Prims.fst"
                                 (Prims.of_int (611)) (Prims.of_int (19))
                                 (Prims.of_int (611)) (Prims.of_int (31)))))
                        (Obj.magic uu___2)
                        (fun uu___3 ->
                           FStar_Tactics_Effect.lift_div_tac
                             (fun uu___4 -> Prims.strcat "Tv_Abs " uu___3))))
            | FStar_Tactics_NamedView.Tv_Arrow (x, c) ->
                Obj.magic
                  (Obj.repr
                     (let uu___2 =
                        let uu___3 =
                          let uu___4 =
                            FStar_Tactics_V2_Derived.binder_to_string x in
                          FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.Print.fst"
                                     (Prims.of_int (49)) (Prims.of_int (41))
                                     (Prims.of_int (49)) (Prims.of_int (59)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.Print.fst"
                                     (Prims.of_int (49)) (Prims.of_int (40))
                                     (Prims.of_int (49)) (Prims.of_int (90)))))
                            (Obj.magic uu___4)
                            (fun uu___5 ->
                               (fun uu___5 ->
                                  let uu___6 =
                                    let uu___7 = comp_to_ast_string c in
                                    FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "FStar.Tactics.Print.fst"
                                               (Prims.of_int (49))
                                               (Prims.of_int (69))
                                               (Prims.of_int (49))
                                               (Prims.of_int (89)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range "Prims.fst"
                                               (Prims.of_int (611))
                                               (Prims.of_int (19))
                                               (Prims.of_int (611))
                                               (Prims.of_int (31)))))
                                      (Obj.magic uu___7)
                                      (fun uu___8 ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___9 ->
                                              Prims.strcat ", " uu___8)) in
                                  Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.Print.fst"
                                                (Prims.of_int (49))
                                                (Prims.of_int (62))
                                                (Prims.of_int (49))
                                                (Prims.of_int (89)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Prims.fst"
                                                (Prims.of_int (611))
                                                (Prims.of_int (19))
                                                (Prims.of_int (611))
                                                (Prims.of_int (31)))))
                                       (Obj.magic uu___6)
                                       (fun uu___7 ->
                                          FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___8 ->
                                               Prims.strcat uu___5 uu___7))))
                                 uu___5) in
                        FStar_Tactics_Effect.tac_bind
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "FStar.Tactics.Print.fst"
                                   (Prims.of_int (49)) (Prims.of_int (40))
                                   (Prims.of_int (49)) (Prims.of_int (90)))))
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "FStar.Tactics.Print.fst"
                                   (Prims.of_int (49)) (Prims.of_int (34))
                                   (Prims.of_int (49)) (Prims.of_int (90)))))
                          (Obj.magic uu___3)
                          (fun uu___4 ->
                             FStar_Tactics_Effect.lift_div_tac
                               (fun uu___5 -> paren uu___4)) in
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                                 (Prims.of_int (49)) (Prims.of_int (34))
                                 (Prims.of_int (49)) (Prims.of_int (90)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "Prims.fst"
                                 (Prims.of_int (611)) (Prims.of_int (19))
                                 (Prims.of_int (611)) (Prims.of_int (31)))))
                        (Obj.magic uu___2)
                        (fun uu___3 ->
                           FStar_Tactics_Effect.lift_div_tac
                             (fun uu___4 -> Prims.strcat "Tv_Arrow " uu___3))))
            | FStar_Tactics_NamedView.Tv_Type u ->
                Obj.magic
                  (Obj.repr
                     (let uu___2 =
                        let uu___3 = universe_to_ast_string u in
                        FStar_Tactics_Effect.tac_bind
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "FStar.Tactics.Print.fst"
                                   (Prims.of_int (50)) (Prims.of_int (32))
                                   (Prims.of_int (50)) (Prims.of_int (58)))))
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "FStar.Tactics.Print.fst"
                                   (Prims.of_int (50)) (Prims.of_int (26))
                                   (Prims.of_int (50)) (Prims.of_int (58)))))
                          (Obj.magic uu___3)
                          (fun uu___4 ->
                             FStar_Tactics_Effect.lift_div_tac
                               (fun uu___5 -> paren uu___4)) in
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                                 (Prims.of_int (50)) (Prims.of_int (26))
                                 (Prims.of_int (50)) (Prims.of_int (58)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "Prims.fst"
                                 (Prims.of_int (611)) (Prims.of_int (19))
                                 (Prims.of_int (611)) (Prims.of_int (31)))))
                        (Obj.magic uu___2)
                        (fun uu___3 ->
                           FStar_Tactics_Effect.lift_div_tac
                             (fun uu___4 -> Prims.strcat "Type" uu___3))))
            | FStar_Tactics_NamedView.Tv_Refine (x, e) ->
                Obj.magic
                  (Obj.repr
                     (let uu___2 =
                        let uu___3 =
                          let uu___4 =
                            FStar_Tactics_V2_Derived.binder_to_string x in
                          FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.Print.fst"
                                     (Prims.of_int (51)) (Prims.of_int (43))
                                     (Prims.of_int (51)) (Prims.of_int (61)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.Print.fst"
                                     (Prims.of_int (51)) (Prims.of_int (42))
                                     (Prims.of_int (51)) (Prims.of_int (92)))))
                            (Obj.magic uu___4)
                            (fun uu___5 ->
                               (fun uu___5 ->
                                  let uu___6 =
                                    let uu___7 = term_to_ast_string e in
                                    FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "FStar.Tactics.Print.fst"
                                               (Prims.of_int (51))
                                               (Prims.of_int (71))
                                               (Prims.of_int (51))
                                               (Prims.of_int (91)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range "Prims.fst"
                                               (Prims.of_int (611))
                                               (Prims.of_int (19))
                                               (Prims.of_int (611))
                                               (Prims.of_int (31)))))
                                      (Obj.magic uu___7)
                                      (fun uu___8 ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___9 ->
                                              Prims.strcat ", " uu___8)) in
                                  Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.Print.fst"
                                                (Prims.of_int (51))
                                                (Prims.of_int (64))
                                                (Prims.of_int (51))
                                                (Prims.of_int (91)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Prims.fst"
                                                (Prims.of_int (611))
                                                (Prims.of_int (19))
                                                (Prims.of_int (611))
                                                (Prims.of_int (31)))))
                                       (Obj.magic uu___6)
                                       (fun uu___7 ->
                                          FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___8 ->
                                               Prims.strcat uu___5 uu___7))))
                                 uu___5) in
                        FStar_Tactics_Effect.tac_bind
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "FStar.Tactics.Print.fst"
                                   (Prims.of_int (51)) (Prims.of_int (42))
                                   (Prims.of_int (51)) (Prims.of_int (92)))))
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "FStar.Tactics.Print.fst"
                                   (Prims.of_int (51)) (Prims.of_int (36))
                                   (Prims.of_int (51)) (Prims.of_int (92)))))
                          (Obj.magic uu___3)
                          (fun uu___4 ->
                             FStar_Tactics_Effect.lift_div_tac
                               (fun uu___5 -> paren uu___4)) in
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                                 (Prims.of_int (51)) (Prims.of_int (36))
                                 (Prims.of_int (51)) (Prims.of_int (92)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "Prims.fst"
                                 (Prims.of_int (611)) (Prims.of_int (19))
                                 (Prims.of_int (611)) (Prims.of_int (31)))))
                        (Obj.magic uu___2)
                        (fun uu___3 ->
                           FStar_Tactics_Effect.lift_div_tac
                             (fun uu___4 -> Prims.strcat "Tv_Refine " uu___3))))
            | FStar_Tactics_NamedView.Tv_Const c ->
                Obj.magic (Obj.repr (const_to_ast_string c))
            | FStar_Tactics_NamedView.Tv_Uvar (i, uu___2) ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___3 ->
                           Prims.strcat "Tv_Uvar " (Prims.string_of_int i))))
            | FStar_Tactics_NamedView.Tv_Let (recf, uu___2, x, e1, e2) ->
                Obj.magic
                  (Obj.repr
                     (let uu___3 =
                        let uu___4 =
                          let uu___5 =
                            let uu___6 =
                              let uu___7 =
                                FStar_Tactics_V2_Derived.binder_to_string x in
                              FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.Print.fst"
                                         (Prims.of_int (56))
                                         (Prims.of_int (30))
                                         (Prims.of_int (56))
                                         (Prims.of_int (48)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.Print.fst"
                                         (Prims.of_int (56))
                                         (Prims.of_int (30))
                                         (Prims.of_int (58))
                                         (Prims.of_int (51)))))
                                (Obj.magic uu___7)
                                (fun uu___8 ->
                                   (fun uu___8 ->
                                      let uu___9 =
                                        let uu___10 =
                                          let uu___11 = term_to_ast_string e1 in
                                          FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "FStar.Tactics.Print.fst"
                                                     (Prims.of_int (57))
                                                     (Prims.of_int (30))
                                                     (Prims.of_int (57))
                                                     (Prims.of_int (51)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "FStar.Tactics.Print.fst"
                                                     (Prims.of_int (57))
                                                     (Prims.of_int (30))
                                                     (Prims.of_int (58))
                                                     (Prims.of_int (51)))))
                                            (Obj.magic uu___11)
                                            (fun uu___12 ->
                                               (fun uu___12 ->
                                                  let uu___13 =
                                                    let uu___14 =
                                                      term_to_ast_string e2 in
                                                    FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "FStar.Tactics.Print.fst"
                                                               (Prims.of_int (58))
                                                               (Prims.of_int (30))
                                                               (Prims.of_int (58))
                                                               (Prims.of_int (51)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Prims.fst"
                                                               (Prims.of_int (611))
                                                               (Prims.of_int (19))
                                                               (Prims.of_int (611))
                                                               (Prims.of_int (31)))))
                                                      (Obj.magic uu___14)
                                                      (fun uu___15 ->
                                                         FStar_Tactics_Effect.lift_div_tac
                                                           (fun uu___16 ->
                                                              Prims.strcat
                                                                ", " uu___15)) in
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "FStar.Tactics.Print.fst"
                                                                (Prims.of_int (57))
                                                                (Prims.of_int (54))
                                                                (Prims.of_int (58))
                                                                (Prims.of_int (51)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Prims.fst"
                                                                (Prims.of_int (611))
                                                                (Prims.of_int (19))
                                                                (Prims.of_int (611))
                                                                (Prims.of_int (31)))))
                                                       (Obj.magic uu___13)
                                                       (fun uu___14 ->
                                                          FStar_Tactics_Effect.lift_div_tac
                                                            (fun uu___15 ->
                                                               Prims.strcat
                                                                 uu___12
                                                                 uu___14))))
                                                 uu___12) in
                                        FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "FStar.Tactics.Print.fst"
                                                   (Prims.of_int (57))
                                                   (Prims.of_int (30))
                                                   (Prims.of_int (58))
                                                   (Prims.of_int (51)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Prims.fst"
                                                   (Prims.of_int (611))
                                                   (Prims.of_int (19))
                                                   (Prims.of_int (611))
                                                   (Prims.of_int (31)))))
                                          (Obj.magic uu___10)
                                          (fun uu___11 ->
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___12 ->
                                                  Prims.strcat ", " uu___11)) in
                                      Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "FStar.Tactics.Print.fst"
                                                    (Prims.of_int (56))
                                                    (Prims.of_int (51))
                                                    (Prims.of_int (58))
                                                    (Prims.of_int (51)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Prims.fst"
                                                    (Prims.of_int (611))
                                                    (Prims.of_int (19))
                                                    (Prims.of_int (611))
                                                    (Prims.of_int (31)))))
                                           (Obj.magic uu___9)
                                           (fun uu___10 ->
                                              FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___11 ->
                                                   Prims.strcat uu___8
                                                     uu___10)))) uu___8) in
                            FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "FStar.Tactics.Print.fst"
                                       (Prims.of_int (56))
                                       (Prims.of_int (30))
                                       (Prims.of_int (58))
                                       (Prims.of_int (51)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range "Prims.fst"
                                       (Prims.of_int (611))
                                       (Prims.of_int (19))
                                       (Prims.of_int (611))
                                       (Prims.of_int (31)))))
                              (Obj.magic uu___6)
                              (fun uu___7 ->
                                 FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___8 -> Prims.strcat ", " uu___7)) in
                          FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.Print.fst"
                                     (Prims.of_int (55)) (Prims.of_int (52))
                                     (Prims.of_int (58)) (Prims.of_int (51)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range "Prims.fst"
                                     (Prims.of_int (611)) (Prims.of_int (19))
                                     (Prims.of_int (611)) (Prims.of_int (31)))))
                            (Obj.magic uu___5)
                            (fun uu___6 ->
                               FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___7 ->
                                    Prims.strcat (Prims.string_of_bool recf)
                                      uu___6)) in
                        FStar_Tactics_Effect.tac_bind
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "FStar.Tactics.Print.fst"
                                   (Prims.of_int (55)) (Prims.of_int (29))
                                   (Prims.of_int (58)) (Prims.of_int (52)))))
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "FStar.Tactics.Print.fst"
                                   (Prims.of_int (55)) (Prims.of_int (23))
                                   (Prims.of_int (58)) (Prims.of_int (52)))))
                          (Obj.magic uu___4)
                          (fun uu___5 ->
                             FStar_Tactics_Effect.lift_div_tac
                               (fun uu___6 -> paren uu___5)) in
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                                 (Prims.of_int (55)) (Prims.of_int (23))
                                 (Prims.of_int (58)) (Prims.of_int (52)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "Prims.fst"
                                 (Prims.of_int (611)) (Prims.of_int (19))
                                 (Prims.of_int (611)) (Prims.of_int (31)))))
                        (Obj.magic uu___3)
                        (fun uu___4 ->
                           FStar_Tactics_Effect.lift_div_tac
                             (fun uu___5 -> Prims.strcat "Tv_Let " uu___4))))
            | FStar_Tactics_NamedView.Tv_Match (e, ret_opt, brs) ->
                Obj.magic
                  (Obj.repr
                     (let uu___2 =
                        let uu___3 =
                          let uu___4 = term_to_ast_string e in
                          FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.Print.fst"
                                     (Prims.of_int (62)) (Prims.of_int (8))
                                     (Prims.of_int (62)) (Prims.of_int (28)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.Print.fst"
                                     (Prims.of_int (61)) (Prims.of_int (12))
                                     (Prims.of_int (66)) (Prims.of_int (35)))))
                            (Obj.magic uu___4)
                            (fun uu___5 ->
                               (fun uu___5 ->
                                  let uu___6 =
                                    let uu___7 =
                                      let uu___8 =
                                        match_returns_to_string ret_opt in
                                      FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "FStar.Tactics.Print.fst"
                                                 (Prims.of_int (64))
                                                 (Prims.of_int (8))
                                                 (Prims.of_int (64))
                                                 (Prims.of_int (39)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "FStar.Tactics.Print.fst"
                                                 (Prims.of_int (64))
                                                 (Prims.of_int (8))
                                                 (Prims.of_int (66))
                                                 (Prims.of_int (34)))))
                                        (Obj.magic uu___8)
                                        (fun uu___9 ->
                                           (fun uu___9 ->
                                              let uu___10 =
                                                let uu___11 =
                                                  branches_to_ast_string brs in
                                                FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.Tactics.Print.fst"
                                                           (Prims.of_int (66))
                                                           (Prims.of_int (8))
                                                           (Prims.of_int (66))
                                                           (Prims.of_int (34)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Prims.fst"
                                                           (Prims.of_int (611))
                                                           (Prims.of_int (19))
                                                           (Prims.of_int (611))
                                                           (Prims.of_int (31)))))
                                                  (Obj.magic uu___11)
                                                  (fun uu___12 ->
                                                     FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___13 ->
                                                          Prims.strcat ", "
                                                            uu___12)) in
                                              Obj.magic
                                                (FStar_Tactics_Effect.tac_bind
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "FStar.Tactics.Print.fst"
                                                            (Prims.of_int (65))
                                                            (Prims.of_int (8))
                                                            (Prims.of_int (66))
                                                            (Prims.of_int (34)))))
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "Prims.fst"
                                                            (Prims.of_int (611))
                                                            (Prims.of_int (19))
                                                            (Prims.of_int (611))
                                                            (Prims.of_int (31)))))
                                                   (Obj.magic uu___10)
                                                   (fun uu___11 ->
                                                      FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___12 ->
                                                           Prims.strcat
                                                             uu___9 uu___11))))
                                             uu___9) in
                                    FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "FStar.Tactics.Print.fst"
                                               (Prims.of_int (64))
                                               (Prims.of_int (8))
                                               (Prims.of_int (66))
                                               (Prims.of_int (34)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range "Prims.fst"
                                               (Prims.of_int (611))
                                               (Prims.of_int (19))
                                               (Prims.of_int (611))
                                               (Prims.of_int (31)))))
                                      (Obj.magic uu___7)
                                      (fun uu___8 ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___9 ->
                                              Prims.strcat ", " uu___8)) in
                                  Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.Print.fst"
                                                (Prims.of_int (63))
                                                (Prims.of_int (8))
                                                (Prims.of_int (66))
                                                (Prims.of_int (34)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Prims.fst"
                                                (Prims.of_int (611))
                                                (Prims.of_int (19))
                                                (Prims.of_int (611))
                                                (Prims.of_int (31)))))
                                       (Obj.magic uu___6)
                                       (fun uu___7 ->
                                          FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___8 ->
                                               Prims.strcat uu___5 uu___7))))
                                 uu___5) in
                        FStar_Tactics_Effect.tac_bind
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "FStar.Tactics.Print.fst"
                                   (Prims.of_int (61)) (Prims.of_int (12))
                                   (Prims.of_int (66)) (Prims.of_int (35)))))
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "FStar.Tactics.Print.fst"
                                   (Prims.of_int (61)) (Prims.of_int (6))
                                   (Prims.of_int (66)) (Prims.of_int (35)))))
                          (Obj.magic uu___3)
                          (fun uu___4 ->
                             FStar_Tactics_Effect.lift_div_tac
                               (fun uu___5 -> paren uu___4)) in
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                                 (Prims.of_int (61)) (Prims.of_int (6))
                                 (Prims.of_int (66)) (Prims.of_int (35)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "Prims.fst"
                                 (Prims.of_int (611)) (Prims.of_int (19))
                                 (Prims.of_int (611)) (Prims.of_int (31)))))
                        (Obj.magic uu___2)
                        (fun uu___3 ->
                           FStar_Tactics_Effect.lift_div_tac
                             (fun uu___4 -> Prims.strcat "Tv_Match " uu___3))))
            | FStar_Tactics_NamedView.Tv_AscribedT (e, t1, uu___2, use_eq) ->
                Obj.magic
                  (Obj.repr
                     (let uu___3 =
                        let uu___4 =
                          let uu___5 = term_to_ast_string e in
                          FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.Print.fst"
                                     (Prims.of_int (67)) (Prims.of_int (58))
                                     (Prims.of_int (67)) (Prims.of_int (78)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.Print.fst"
                                     (Prims.of_int (67)) (Prims.of_int (57))
                                     (Prims.of_int (67)) (Prims.of_int (140)))))
                            (Obj.magic uu___5)
                            (fun uu___6 ->
                               (fun uu___6 ->
                                  let uu___7 =
                                    let uu___8 =
                                      let uu___9 = term_to_ast_string t1 in
                                      FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "FStar.Tactics.Print.fst"
                                                 (Prims.of_int (67))
                                                 (Prims.of_int (88))
                                                 (Prims.of_int (67))
                                                 (Prims.of_int (108)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Prims.fst"
                                                 (Prims.of_int (611))
                                                 (Prims.of_int (19))
                                                 (Prims.of_int (611))
                                                 (Prims.of_int (31)))))
                                        (Obj.magic uu___9)
                                        (fun uu___10 ->
                                           FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___11 ->
                                                Prims.strcat uu___10
                                                  (Prims.strcat ", "
                                                     (Prims.string_of_bool
                                                        use_eq)))) in
                                    FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "FStar.Tactics.Print.fst"
                                               (Prims.of_int (67))
                                               (Prims.of_int (88))
                                               (Prims.of_int (67))
                                               (Prims.of_int (139)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range "Prims.fst"
                                               (Prims.of_int (611))
                                               (Prims.of_int (19))
                                               (Prims.of_int (611))
                                               (Prims.of_int (31)))))
                                      (Obj.magic uu___8)
                                      (fun uu___9 ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___10 ->
                                              Prims.strcat ", " uu___9)) in
                                  Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.Print.fst"
                                                (Prims.of_int (67))
                                                (Prims.of_int (81))
                                                (Prims.of_int (67))
                                                (Prims.of_int (139)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Prims.fst"
                                                (Prims.of_int (611))
                                                (Prims.of_int (19))
                                                (Prims.of_int (611))
                                                (Prims.of_int (31)))))
                                       (Obj.magic uu___7)
                                       (fun uu___8 ->
                                          FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___9 ->
                                               Prims.strcat uu___6 uu___8))))
                                 uu___6) in
                        FStar_Tactics_Effect.tac_bind
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "FStar.Tactics.Print.fst"
                                   (Prims.of_int (67)) (Prims.of_int (57))
                                   (Prims.of_int (67)) (Prims.of_int (140)))))
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "FStar.Tactics.Print.fst"
                                   (Prims.of_int (67)) (Prims.of_int (51))
                                   (Prims.of_int (67)) (Prims.of_int (140)))))
                          (Obj.magic uu___4)
                          (fun uu___5 ->
                             FStar_Tactics_Effect.lift_div_tac
                               (fun uu___6 -> paren uu___5)) in
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                                 (Prims.of_int (67)) (Prims.of_int (51))
                                 (Prims.of_int (67)) (Prims.of_int (140)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "Prims.fst"
                                 (Prims.of_int (611)) (Prims.of_int (19))
                                 (Prims.of_int (611)) (Prims.of_int (31)))))
                        (Obj.magic uu___3)
                        (fun uu___4 ->
                           FStar_Tactics_Effect.lift_div_tac
                             (fun uu___5 ->
                                Prims.strcat "Tv_AscribedT " uu___4))))
            | FStar_Tactics_NamedView.Tv_AscribedC (e, c, uu___2, use_eq) ->
                Obj.magic
                  (Obj.repr
                     (let uu___3 =
                        let uu___4 =
                          let uu___5 = term_to_ast_string e in
                          FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.Print.fst"
                                     (Prims.of_int (68)) (Prims.of_int (58))
                                     (Prims.of_int (68)) (Prims.of_int (78)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.Print.fst"
                                     (Prims.of_int (68)) (Prims.of_int (57))
                                     (Prims.of_int (68)) (Prims.of_int (140)))))
                            (Obj.magic uu___5)
                            (fun uu___6 ->
                               (fun uu___6 ->
                                  let uu___7 =
                                    let uu___8 =
                                      let uu___9 = comp_to_ast_string c in
                                      FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "FStar.Tactics.Print.fst"
                                                 (Prims.of_int (68))
                                                 (Prims.of_int (88))
                                                 (Prims.of_int (68))
                                                 (Prims.of_int (108)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Prims.fst"
                                                 (Prims.of_int (611))
                                                 (Prims.of_int (19))
                                                 (Prims.of_int (611))
                                                 (Prims.of_int (31)))))
                                        (Obj.magic uu___9)
                                        (fun uu___10 ->
                                           FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___11 ->
                                                Prims.strcat uu___10
                                                  (Prims.strcat ", "
                                                     (Prims.string_of_bool
                                                        use_eq)))) in
                                    FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "FStar.Tactics.Print.fst"
                                               (Prims.of_int (68))
                                               (Prims.of_int (88))
                                               (Prims.of_int (68))
                                               (Prims.of_int (139)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range "Prims.fst"
                                               (Prims.of_int (611))
                                               (Prims.of_int (19))
                                               (Prims.of_int (611))
                                               (Prims.of_int (31)))))
                                      (Obj.magic uu___8)
                                      (fun uu___9 ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___10 ->
                                              Prims.strcat ", " uu___9)) in
                                  Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.Print.fst"
                                                (Prims.of_int (68))
                                                (Prims.of_int (81))
                                                (Prims.of_int (68))
                                                (Prims.of_int (139)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Prims.fst"
                                                (Prims.of_int (611))
                                                (Prims.of_int (19))
                                                (Prims.of_int (611))
                                                (Prims.of_int (31)))))
                                       (Obj.magic uu___7)
                                       (fun uu___8 ->
                                          FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___9 ->
                                               Prims.strcat uu___6 uu___8))))
                                 uu___6) in
                        FStar_Tactics_Effect.tac_bind
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "FStar.Tactics.Print.fst"
                                   (Prims.of_int (68)) (Prims.of_int (57))
                                   (Prims.of_int (68)) (Prims.of_int (140)))))
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "FStar.Tactics.Print.fst"
                                   (Prims.of_int (68)) (Prims.of_int (51))
                                   (Prims.of_int (68)) (Prims.of_int (140)))))
                          (Obj.magic uu___4)
                          (fun uu___5 ->
                             FStar_Tactics_Effect.lift_div_tac
                               (fun uu___6 -> paren uu___5)) in
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                                 (Prims.of_int (68)) (Prims.of_int (51))
                                 (Prims.of_int (68)) (Prims.of_int (140)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "Prims.fst"
                                 (Prims.of_int (611)) (Prims.of_int (19))
                                 (Prims.of_int (611)) (Prims.of_int (31)))))
                        (Obj.magic uu___3)
                        (fun uu___4 ->
                           FStar_Tactics_Effect.lift_div_tac
                             (fun uu___5 ->
                                Prims.strcat "Tv_AscribedC " uu___4))))
            | FStar_Tactics_NamedView.Tv_Unknown ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> "_")))
            | FStar_Tactics_NamedView.Tv_Unsupp ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___2 -> "<Tv_Unsupp>")))) uu___1)
and (match_returns_to_string :
  FStar_Tactics_NamedView.match_returns_ascription
    FStar_Pervasives_Native.option ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun ret_opt ->
    let uu___ =
      Obj.magic
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___2 ->
              fun uu___1 ->
                (fun uu___1 ->
                   fun tacopt ->
                     match tacopt with
                     | FStar_Pervasives_Native.None ->
                         Obj.magic
                           (Obj.repr
                              (FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___2 -> "")))
                     | FStar_Pervasives_Native.Some tac ->
                         Obj.magic
                           (Obj.repr
                              (let uu___2 = term_to_ast_string tac in
                               FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "FStar.Tactics.Print.fst"
                                          (Prims.of_int (76))
                                          (Prims.of_int (27))
                                          (Prims.of_int (76))
                                          (Prims.of_int (51)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range "Prims.fst"
                                          (Prims.of_int (611))
                                          (Prims.of_int (19))
                                          (Prims.of_int (611))
                                          (Prims.of_int (31)))))
                                 (Obj.magic uu___2)
                                 (fun uu___3 ->
                                    FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___4 ->
                                         Prims.strcat " by " uu___3)))))
                  uu___2 uu___1)) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.Print.fst"
               (Prims.of_int (74)) (Prims.of_int (4)) (Prims.of_int (76))
               (Prims.of_int (51)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.Print.fst"
               (Prims.of_int (77)) (Prims.of_int (2)) (Prims.of_int (84))
               (Prims.of_int (78))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun tacopt_to_string ->
            match ret_opt with
            | FStar_Pervasives_Native.None ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> "")))
            | FStar_Pervasives_Native.Some (b, asc) ->
                Obj.magic
                  (Obj.repr
                     (let uu___1 =
                        let uu___2 =
                          FStar_Tactics_V2_Derived.binder_to_string b in
                        FStar_Tactics_Effect.tac_bind
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "FStar.Tactics.Print.fst"
                                   (Prims.of_int (80)) (Prims.of_int (5))
                                   (Prims.of_int (80)) (Prims.of_int (23)))))
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range "Prims.fst"
                                   (Prims.of_int (611)) (Prims.of_int (19))
                                   (Prims.of_int (611)) (Prims.of_int (31)))))
                          (Obj.magic uu___2)
                          (fun uu___3 ->
                             FStar_Tactics_Effect.lift_div_tac
                               (fun uu___4 -> Prims.strcat uu___3 " ")) in
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                                 (Prims.of_int (80)) (Prims.of_int (4))
                                 (Prims.of_int (80)) (Prims.of_int (30)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                                 (Prims.of_int (80)) (Prims.of_int (4))
                                 (Prims.of_int (84)) (Prims.of_int (78)))))
                        (Obj.magic uu___1)
                        (fun uu___2 ->
                           (fun uu___2 ->
                              let uu___3 =
                                match asc with
                                | (FStar_Pervasives.Inl t, tacopt, uu___4) ->
                                    let uu___5 = term_to_ast_string t in
                                    FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "FStar.Tactics.Print.fst"
                                               (Prims.of_int (83))
                                               (Prims.of_int (27))
                                               (Prims.of_int (83))
                                               (Prims.of_int (49)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "FStar.Tactics.Print.fst"
                                               (Prims.of_int (83))
                                               (Prims.of_int (27))
                                               (Prims.of_int (83))
                                               (Prims.of_int (77)))))
                                      (Obj.magic uu___5)
                                      (fun uu___6 ->
                                         (fun uu___6 ->
                                            let uu___7 =
                                              tacopt_to_string tacopt in
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "FStar.Tactics.Print.fst"
                                                          (Prims.of_int (83))
                                                          (Prims.of_int (52))
                                                          (Prims.of_int (83))
                                                          (Prims.of_int (77)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Prims.fst"
                                                          (Prims.of_int (611))
                                                          (Prims.of_int (19))
                                                          (Prims.of_int (611))
                                                          (Prims.of_int (31)))))
                                                 (Obj.magic uu___7)
                                                 (fun uu___8 ->
                                                    FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___9 ->
                                                         Prims.strcat uu___6
                                                           uu___8)))) uu___6)
                                | (FStar_Pervasives.Inr c, tacopt, uu___4) ->
                                    let uu___5 = comp_to_ast_string c in
                                    FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "FStar.Tactics.Print.fst"
                                               (Prims.of_int (84))
                                               (Prims.of_int (27))
                                               (Prims.of_int (84))
                                               (Prims.of_int (49)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "FStar.Tactics.Print.fst"
                                               (Prims.of_int (84))
                                               (Prims.of_int (27))
                                               (Prims.of_int (84))
                                               (Prims.of_int (77)))))
                                      (Obj.magic uu___5)
                                      (fun uu___6 ->
                                         (fun uu___6 ->
                                            let uu___7 =
                                              tacopt_to_string tacopt in
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "FStar.Tactics.Print.fst"
                                                          (Prims.of_int (84))
                                                          (Prims.of_int (52))
                                                          (Prims.of_int (84))
                                                          (Prims.of_int (77)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Prims.fst"
                                                          (Prims.of_int (611))
                                                          (Prims.of_int (19))
                                                          (Prims.of_int (611))
                                                          (Prims.of_int (31)))))
                                                 (Obj.magic uu___7)
                                                 (fun uu___8 ->
                                                    FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___9 ->
                                                         Prims.strcat uu___6
                                                           uu___8)))) uu___6) in
                              Obj.magic
                                (FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "FStar.Tactics.Print.fst"
                                            (Prims.of_int (82))
                                            (Prims.of_int (4))
                                            (Prims.of_int (84))
                                            (Prims.of_int (78)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range "Prims.fst"
                                            (Prims.of_int (611))
                                            (Prims.of_int (19))
                                            (Prims.of_int (611))
                                            (Prims.of_int (31)))))
                                   (Obj.magic uu___3)
                                   (fun uu___4 ->
                                      FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___5 ->
                                           Prims.strcat uu___2 uu___4))))
                             uu___2)))) uu___1)
and (branches_to_ast_string :
  FStar_Tactics_NamedView.branch Prims.list ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  = fun brs -> print_list branch_to_ast_string brs
and (branch_to_ast_string :
  FStar_Tactics_NamedView.branch ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun b ->
    let uu___ =
      Obj.magic (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> b)) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.Print.fst"
               (Prims.of_int (90)) (Prims.of_int (13)) (Prims.of_int (90))
               (Prims.of_int (14)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.Print.fst"
               (Prims.of_int (89)) (Prims.of_int (50)) (Prims.of_int (91))
               (Prims.of_int (41))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun uu___1 ->
            match uu___1 with
            | (p, e) ->
                let uu___2 =
                  let uu___3 = term_to_ast_string e in
                  FStar_Tactics_Effect.tac_bind
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                             (Prims.of_int (91)) (Prims.of_int (20))
                             (Prims.of_int (91)) (Prims.of_int (40)))))
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Prims.fst"
                             (Prims.of_int (611)) (Prims.of_int (19))
                             (Prims.of_int (611)) (Prims.of_int (31)))))
                    (Obj.magic uu___3)
                    (fun uu___4 ->
                       FStar_Tactics_Effect.lift_div_tac
                         (fun uu___5 -> Prims.strcat "_pat, " uu___4)) in
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                              (Prims.of_int (91)) (Prims.of_int (8))
                              (Prims.of_int (91)) (Prims.of_int (41)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                              (Prims.of_int (91)) (Prims.of_int (2))
                              (Prims.of_int (91)) (Prims.of_int (41)))))
                     (Obj.magic uu___2)
                     (fun uu___3 ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___4 -> paren uu___3)))) uu___1)
and (comp_to_ast_string :
  FStar_Tactics_NamedView.comp ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun c ->
    match FStar_Tactics_NamedView.inspect_comp c with
    | FStarC_Reflection_V2_Data.C_Total t ->
        let uu___ = term_to_ast_string t in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                   (Prims.of_int (95)) (Prims.of_int (26))
                   (Prims.of_int (95)) (Prims.of_int (46)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Prims.fst" (Prims.of_int (611))
                   (Prims.of_int (19)) (Prims.of_int (611))
                   (Prims.of_int (31))))) (Obj.magic uu___)
          (fun uu___1 ->
             FStar_Tactics_Effect.lift_div_tac
               (fun uu___2 -> Prims.strcat "Tot " uu___1))
    | FStarC_Reflection_V2_Data.C_GTotal t ->
        let uu___ = term_to_ast_string t in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                   (Prims.of_int (96)) (Prims.of_int (28))
                   (Prims.of_int (96)) (Prims.of_int (48)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Prims.fst" (Prims.of_int (611))
                   (Prims.of_int (19)) (Prims.of_int (611))
                   (Prims.of_int (31))))) (Obj.magic uu___)
          (fun uu___1 ->
             FStar_Tactics_Effect.lift_div_tac
               (fun uu___2 -> Prims.strcat "GTot " uu___1))
    | FStarC_Reflection_V2_Data.C_Lemma (pre, post, uu___) ->
        let uu___1 =
          let uu___2 = term_to_ast_string pre in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                     (Prims.of_int (97)) (Prims.of_int (37))
                     (Prims.of_int (97)) (Prims.of_int (59)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                     (Prims.of_int (97)) (Prims.of_int (37))
                     (Prims.of_int (97)) (Prims.of_int (91)))))
            (Obj.magic uu___2)
            (fun uu___3 ->
               (fun uu___3 ->
                  let uu___4 =
                    let uu___5 = term_to_ast_string post in
                    FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                               (Prims.of_int (97)) (Prims.of_int (68))
                               (Prims.of_int (97)) (Prims.of_int (91)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Prims.fst"
                               (Prims.of_int (611)) (Prims.of_int (19))
                               (Prims.of_int (611)) (Prims.of_int (31)))))
                      (Obj.magic uu___5)
                      (fun uu___6 ->
                         FStar_Tactics_Effect.lift_div_tac
                           (fun uu___7 -> Prims.strcat " " uu___6)) in
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                                (Prims.of_int (97)) (Prims.of_int (62))
                                (Prims.of_int (97)) (Prims.of_int (91)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Prims.fst"
                                (Prims.of_int (611)) (Prims.of_int (19))
                                (Prims.of_int (611)) (Prims.of_int (31)))))
                       (Obj.magic uu___4)
                       (fun uu___5 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___6 -> Prims.strcat uu___3 uu___5))))
                 uu___3) in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                   (Prims.of_int (97)) (Prims.of_int (37))
                   (Prims.of_int (97)) (Prims.of_int (91)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Prims.fst" (Prims.of_int (611))
                   (Prims.of_int (19)) (Prims.of_int (611))
                   (Prims.of_int (31))))) (Obj.magic uu___1)
          (fun uu___2 ->
             FStar_Tactics_Effect.lift_div_tac
               (fun uu___3 -> Prims.strcat "Lemma " uu___2))
    | FStarC_Reflection_V2_Data.C_Eff (us, eff, res, uu___, uu___1) ->
        let uu___2 =
          let uu___3 =
            let uu___4 = universes_to_ast_string us in
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                       (Prims.of_int (99)) (Prims.of_int (21))
                       (Prims.of_int (99)) (Prims.of_int (47)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                       (Prims.of_int (99)) (Prims.of_int (21))
                       (Prims.of_int (99)) (Prims.of_int (111)))))
              (Obj.magic uu___4)
              (fun uu___5 ->
                 (fun uu___5 ->
                    let uu___6 =
                      let uu___7 =
                        let uu___8 =
                          let uu___9 =
                            let uu___10 = term_to_ast_string res in
                            FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "FStar.Tactics.Print.fst"
                                       (Prims.of_int (99))
                                       (Prims.of_int (88))
                                       (Prims.of_int (99))
                                       (Prims.of_int (110)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range "Prims.fst"
                                       (Prims.of_int (611))
                                       (Prims.of_int (19))
                                       (Prims.of_int (611))
                                       (Prims.of_int (31)))))
                              (Obj.magic uu___10)
                              (fun uu___11 ->
                                 FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___12 -> Prims.strcat ", " uu___11)) in
                          FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.Print.fst"
                                     (Prims.of_int (99)) (Prims.of_int (81))
                                     (Prims.of_int (99)) (Prims.of_int (110)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range "Prims.fst"
                                     (Prims.of_int (611)) (Prims.of_int (19))
                                     (Prims.of_int (611)) (Prims.of_int (31)))))
                            (Obj.magic uu___9)
                            (fun uu___10 ->
                               FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___11 ->
                                    Prims.strcat
                                      (FStarC_Reflection_V2_Builtins.implode_qn
                                         eff) uu___10)) in
                        FStar_Tactics_Effect.tac_bind
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "FStar.Tactics.Print.fst"
                                   (Prims.of_int (99)) (Prims.of_int (63))
                                   (Prims.of_int (99)) (Prims.of_int (111)))))
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "FStar.Tactics.Print.fst"
                                   (Prims.of_int (99)) (Prims.of_int (57))
                                   (Prims.of_int (99)) (Prims.of_int (111)))))
                          (Obj.magic uu___8)
                          (fun uu___9 ->
                             FStar_Tactics_Effect.lift_div_tac
                               (fun uu___10 -> paren uu___9)) in
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                                 (Prims.of_int (99)) (Prims.of_int (57))
                                 (Prims.of_int (99)) (Prims.of_int (111)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "Prims.fst"
                                 (Prims.of_int (611)) (Prims.of_int (19))
                                 (Prims.of_int (611)) (Prims.of_int (31)))))
                        (Obj.magic uu___7)
                        (fun uu___8 ->
                           FStar_Tactics_Effect.lift_div_tac
                             (fun uu___9 -> Prims.strcat "> " uu___8)) in
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.Tactics.Print.fst"
                                  (Prims.of_int (99)) (Prims.of_int (50))
                                  (Prims.of_int (99)) (Prims.of_int (111)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range "Prims.fst"
                                  (Prims.of_int (611)) (Prims.of_int (19))
                                  (Prims.of_int (611)) (Prims.of_int (31)))))
                         (Obj.magic uu___6)
                         (fun uu___7 ->
                            FStar_Tactics_Effect.lift_div_tac
                              (fun uu___8 -> Prims.strcat uu___5 uu___7))))
                   uu___5) in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                     (Prims.of_int (99)) (Prims.of_int (21))
                     (Prims.of_int (99)) (Prims.of_int (111)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Prims.fst" (Prims.of_int (611))
                     (Prims.of_int (19)) (Prims.of_int (611))
                     (Prims.of_int (31))))) (Obj.magic uu___3)
            (fun uu___4 ->
               FStar_Tactics_Effect.lift_div_tac
                 (fun uu___5 -> Prims.strcat "<" uu___4)) in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.Print.fst"
                   (Prims.of_int (99)) (Prims.of_int (15))
                   (Prims.of_int (99)) (Prims.of_int (111)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Prims.fst" (Prims.of_int (611))
                   (Prims.of_int (19)) (Prims.of_int (611))
                   (Prims.of_int (31))))) (Obj.magic uu___2)
          (fun uu___3 ->
             FStar_Tactics_Effect.lift_div_tac
               (fun uu___4 -> Prims.strcat "Effect" uu___3))
and (const_to_ast_string :
  FStarC_Reflection_V2_Data.vconst ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    (fun c ->
       Obj.magic
         (FStar_Tactics_Effect.lift_div_tac
            (fun uu___ ->
               match c with
               | FStarC_Reflection_V2_Data.C_Unit -> "C_Unit"
               | FStarC_Reflection_V2_Data.C_Int i ->
                   Prims.strcat "C_Int " (Prims.string_of_int i)
               | FStarC_Reflection_V2_Data.C_True -> "C_True"
               | FStarC_Reflection_V2_Data.C_False -> "C_False"
               | FStarC_Reflection_V2_Data.C_String s ->
                   Prims.strcat "C_String " s
               | FStarC_Reflection_V2_Data.C_Range uu___1 -> "C_Range _"
               | FStarC_Reflection_V2_Data.C_Reify -> "C_Reify"
               | FStarC_Reflection_V2_Data.C_Reflect name ->
                   Prims.strcat "C_Reflect "
                     (FStarC_Reflection_V2_Builtins.implode_qn name)
               | FStarC_Reflection_V2_Data.C_Real r ->
                   Prims.strcat "C_Real \"" (Prims.strcat r "\"")))) uu___
let _ =
  FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.Print.term_to_ast_string" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.Print.term_to_ast_string (plugin)"
               (FStarC_Tactics_Native.from_tactic_1 term_to_ast_string)
               FStarC_Reflection_V2_Embeddings.e_term
               FStarC_Syntax_Embeddings.e_string psc ncb us args)
let _ =
  FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.Print.match_returns_to_string" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.Print.match_returns_to_string (plugin)"
               (FStarC_Tactics_Native.from_tactic_1 match_returns_to_string)
               (FStarC_Syntax_Embeddings.e_option
                  (FStarC_Syntax_Embeddings.e_tuple2
                     FStar_Tactics_NamedView.e_binder
                     (FStarC_Syntax_Embeddings.e_tuple3
                        (FStarC_Syntax_Embeddings.e_either
                           FStarC_Reflection_V2_Embeddings.e_term
                           FStarC_Reflection_V2_Embeddings.e_comp_view)
                        (FStarC_Syntax_Embeddings.e_option
                           FStarC_Reflection_V2_Embeddings.e_term)
                        FStarC_Syntax_Embeddings.e_bool)))
               FStarC_Syntax_Embeddings.e_string psc ncb us args)
let _ =
  FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.Print.branches_to_ast_string" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.Print.branches_to_ast_string (plugin)"
               (FStarC_Tactics_Native.from_tactic_1 branches_to_ast_string)
               (FStarC_Syntax_Embeddings.e_list
                  (FStarC_Syntax_Embeddings.e_tuple2
                     FStar_Tactics_NamedView.e_pattern
                     FStarC_Reflection_V2_Embeddings.e_term))
               FStarC_Syntax_Embeddings.e_string psc ncb us args)
let _ =
  FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.Print.branch_to_ast_string" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.Print.branch_to_ast_string (plugin)"
               (FStarC_Tactics_Native.from_tactic_1 branch_to_ast_string)
               (FStarC_Syntax_Embeddings.e_tuple2
                  FStar_Tactics_NamedView.e_pattern
                  FStarC_Reflection_V2_Embeddings.e_term)
               FStarC_Syntax_Embeddings.e_string psc ncb us args)
let _ =
  FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.Print.comp_to_ast_string" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.Print.comp_to_ast_string (plugin)"
               (FStarC_Tactics_Native.from_tactic_1 comp_to_ast_string)
               FStarC_Reflection_V2_Embeddings.e_comp_view
               FStarC_Syntax_Embeddings.e_string psc ncb us args)
let _ =
  FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.Print.const_to_ast_string" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.Print.const_to_ast_string (plugin)"
               (FStarC_Tactics_Native.from_tactic_1 const_to_ast_string)
               FStarC_Reflection_V2_Embeddings.e_vconst
               FStarC_Syntax_Embeddings.e_string psc ncb us args)