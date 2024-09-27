open Prims
let (tot_or_ghost_to_string :
  FStar_TypeChecker_Core.tot_or_ghost -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | FStar_TypeChecker_Core.E_Total -> "total"
    | FStar_TypeChecker_Core.E_Ghost -> "ghost"
let (name_to_string : FStar_Reflection_Types.name -> Prims.string) =
  fun f -> FStar_String.concat "." f
let (dbg_printing : Prims.bool) = true
let rec (universe_to_string :
  Prims.nat -> Pulse_Syntax_Base.universe -> Prims.string) =
  fun n ->
    fun u ->
      match FStar_Reflection_V2_Builtins.inspect_universe u with
      | FStar_Reflection_V2_Data.Uv_Unk -> "_"
      | FStar_Reflection_V2_Data.Uv_Zero ->
          Prims.strcat "" (Prims.strcat (Prims.string_of_int n) "")
      | FStar_Reflection_V2_Data.Uv_Succ u1 ->
          universe_to_string (n + Prims.int_one) u1
      | FStar_Reflection_V2_Data.Uv_BVar x ->
          if n = Prims.int_zero
          then Prims.strcat "" (Prims.strcat (Prims.string_of_int x) "")
          else
            Prims.strcat
              (Prims.strcat "(" (Prims.strcat (Prims.string_of_int x) " + "))
              (Prims.strcat (Prims.string_of_int n) ")")
      | FStar_Reflection_V2_Data.Uv_Max us ->
          let r = "(max _)" in
          if n = Prims.int_zero
          then r
          else
            Prims.strcat (Prims.strcat "" (Prims.strcat r " + "))
              (Prims.strcat (Prims.string_of_int n) "")
      | uu___ -> "<univ>"
let (univ_to_string : Pulse_Syntax_Base.universe -> Prims.string) =
  fun u ->
    Prims.strcat "u#" (Prims.strcat (universe_to_string Prims.int_zero u) "")
let (qual_to_string :
  Pulse_Syntax_Base.qualifier FStar_Pervasives_Native.option -> Prims.string)
  =
  fun uu___ ->
    match uu___ with
    | FStar_Pervasives_Native.None -> ""
    | FStar_Pervasives_Native.Some (Pulse_Syntax_Base.Implicit) -> "#"
    | FStar_Pervasives_Native.Some (Pulse_Syntax_Base.TcArg) ->
        "#[tcresolve]"
let (indent : Prims.string -> Prims.string) =
  fun level -> Prims.strcat level "\t"
let rec (collect_binders :
  (Pulse_Syntax_Pure.term_view -> Prims.bool) ->
    Pulse_Syntax_Base.term ->
      (Pulse_Syntax_Base.binder Prims.list * Pulse_Syntax_Base.term))
  =
  fun until ->
    fun t ->
      let tv = Pulse_Syntax_Pure.inspect_term t in
      if Prims.op_Negation (until tv)
      then ([], t)
      else
        (match tv with
         | Pulse_Syntax_Pure.Tm_ExistsSL (uu___1, b, body) ->
             let uu___2 = collect_binders until body in
             (match uu___2 with | (bs, t1) -> ((b :: bs), t1))
         | Pulse_Syntax_Pure.Tm_ForallSL (uu___1, b, body) ->
             let uu___2 = collect_binders until body in
             (match uu___2 with | (bs, t1) -> ((b :: bs), t1))
         | uu___1 -> ([], t))
let rec (binder_to_string_paren :
  Pulse_Syntax_Base.binder ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun b ->
    let uu___ = term_to_string' "" b.Pulse_Syntax_Base.binder_ty in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
               (Prims.of_int (83)) (Prims.of_int (12)) (Prims.of_int (83))
               (Prims.of_int (44)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
               (Prims.of_int (78)) (Prims.of_int (4)) (Prims.of_int (83))
               (Prims.of_int (44))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun uu___1 ->
            let uu___2 =
              let uu___3 =
                FStar_Tactics_Unseal.unseal
                  (b.Pulse_Syntax_Base.binder_ppname).Pulse_Syntax_Base.name in
              FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                         (Prims.of_int (82)) (Prims.of_int (12))
                         (Prims.of_int (82)) (Prims.of_int (43)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                         (Prims.of_int (78)) (Prims.of_int (4))
                         (Prims.of_int (83)) (Prims.of_int (44)))))
                (Obj.magic uu___3)
                (fun uu___4 ->
                   (fun uu___4 ->
                      let uu___5 =
                        let uu___6 =
                          let uu___7 =
                            FStar_Tactics_Unseal.unseal
                              b.Pulse_Syntax_Base.binder_attrs in
                          FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "Pulse.Syntax.Printer.fst"
                                     (Prims.of_int (79)) (Prims.of_int (19))
                                     (Prims.of_int (79)) (Prims.of_int (42)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "Pulse.Syntax.Printer.fst"
                                     (Prims.of_int (79)) (Prims.of_int (12))
                                     (Prims.of_int (81)) (Prims.of_int (91)))))
                            (Obj.magic uu___7)
                            (fun uu___8 ->
                               (fun uu___8 ->
                                  match uu___8 with
                                  | [] ->
                                      Obj.magic
                                        (Obj.repr
                                           (FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___9 -> "")))
                                  | l ->
                                      Obj.magic
                                        (Obj.repr
                                           (let uu___9 =
                                              let uu___10 =
                                                FStar_Tactics_Util.map
                                                  (term_to_string' "") l in
                                              FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Syntax.Printer.fst"
                                                         (Prims.of_int (81))
                                                         (Prims.of_int (59))
                                                         (Prims.of_int (81))
                                                         (Prims.of_int (89)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Syntax.Printer.fst"
                                                         (Prims.of_int (81))
                                                         (Prims.of_int (40))
                                                         (Prims.of_int (81))
                                                         (Prims.of_int (90)))))
                                                (Obj.magic uu___10)
                                                (fun uu___11 ->
                                                   FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___12 ->
                                                        FStar_String.concat
                                                          ";" uu___11)) in
                                            FStar_Tactics_Effect.tac_bind
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Syntax.Printer.fst"
                                                       (Prims.of_int (81))
                                                       (Prims.of_int (40))
                                                       (Prims.of_int (81))
                                                       (Prims.of_int (90)))))
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
                                                      Prims.strcat "[@@@ "
                                                        (Prims.strcat uu___10
                                                           "] ")))))) uu___8) in
                        FStar_Tactics_Effect.tac_bind
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "Pulse.Syntax.Printer.fst"
                                   (Prims.of_int (79)) (Prims.of_int (12))
                                   (Prims.of_int (81)) (Prims.of_int (91)))))
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range "FStar.Printf.fst"
                                   (Prims.of_int (122)) (Prims.of_int (8))
                                   (Prims.of_int (124)) (Prims.of_int (44)))))
                          (Obj.magic uu___6)
                          (fun uu___7 ->
                             FStar_Tactics_Effect.lift_div_tac
                               (fun uu___8 ->
                                  fun x ->
                                    fun x1 ->
                                      Prims.strcat
                                        (Prims.strcat
                                           (Prims.strcat "("
                                              (Prims.strcat uu___7 ""))
                                           (Prims.strcat x ":"))
                                        (Prims.strcat x1 ")"))) in
                      Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Syntax.Printer.fst"
                                    (Prims.of_int (78)) (Prims.of_int (4))
                                    (Prims.of_int (83)) (Prims.of_int (44)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Syntax.Printer.fst"
                                    (Prims.of_int (78)) (Prims.of_int (4))
                                    (Prims.of_int (83)) (Prims.of_int (44)))))
                           (Obj.magic uu___5)
                           (fun uu___6 ->
                              FStar_Tactics_Effect.lift_div_tac
                                (fun uu___7 -> uu___6 uu___4)))) uu___4) in
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                          (Prims.of_int (78)) (Prims.of_int (4))
                          (Prims.of_int (83)) (Prims.of_int (44)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                          (Prims.of_int (78)) (Prims.of_int (4))
                          (Prims.of_int (83)) (Prims.of_int (44)))))
                 (Obj.magic uu___2)
                 (fun uu___3 ->
                    FStar_Tactics_Effect.lift_div_tac
                      (fun uu___4 -> uu___3 uu___1)))) uu___1)
and (term_to_string' :
  Prims.string ->
    Pulse_Syntax_Base.term ->
      (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun level ->
         fun t ->
           match Pulse_Syntax_Pure.inspect_term t with
           | Pulse_Syntax_Pure.Tm_Emp ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> "emp")))
           | Pulse_Syntax_Pure.Tm_Pure p ->
               Obj.magic
                 (Obj.repr
                    (let uu___ = term_to_string' (indent level) p in
                     FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                                (Prims.of_int (91)) (Prims.of_int (8))
                                (Prims.of_int (91)) (Prims.of_int (42)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Prims.fst"
                                (Prims.of_int (611)) (Prims.of_int (19))
                                (Prims.of_int (611)) (Prims.of_int (31)))))
                       (Obj.magic uu___)
                       (fun uu___1 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___2 ->
                               Prims.strcat "pure ("
                                 (Prims.strcat uu___1 ")")))))
           | Pulse_Syntax_Pure.Tm_Star (p1, p2) ->
               Obj.magic
                 (Obj.repr
                    (let uu___ = term_to_string' level p2 in
                     FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                                (Prims.of_int (97)) (Prims.of_int (8))
                                (Prims.of_int (97)) (Prims.of_int (34)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                                (Prims.of_int (94)) (Prims.of_int (6))
                                (Prims.of_int (97)) (Prims.of_int (34)))))
                       (Obj.magic uu___)
                       (fun uu___1 ->
                          (fun uu___1 ->
                             let uu___2 =
                               let uu___3 =
                                 let uu___4 = term_to_string' level p1 in
                                 FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Syntax.Printer.fst"
                                            (Prims.of_int (95))
                                            (Prims.of_int (8))
                                            (Prims.of_int (95))
                                            (Prims.of_int (34)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "FStar.Printf.fst"
                                            (Prims.of_int (122))
                                            (Prims.of_int (8))
                                            (Prims.of_int (124))
                                            (Prims.of_int (44)))))
                                   (Obj.magic uu___4)
                                   (fun uu___5 ->
                                      FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___6 ->
                                           fun x ->
                                             fun x1 ->
                                               Prims.strcat
                                                 (Prims.strcat
                                                    (Prims.strcat ""
                                                       (Prims.strcat uu___5
                                                          " ** \n"))
                                                    (Prims.strcat x ""))
                                                 (Prims.strcat x1 ""))) in
                               FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Syntax.Printer.fst"
                                          (Prims.of_int (94))
                                          (Prims.of_int (6))
                                          (Prims.of_int (97))
                                          (Prims.of_int (34)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Syntax.Printer.fst"
                                          (Prims.of_int (94))
                                          (Prims.of_int (6))
                                          (Prims.of_int (97))
                                          (Prims.of_int (34)))))
                                 (Obj.magic uu___3)
                                 (fun uu___4 ->
                                    FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___5 -> uu___4 level)) in
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Syntax.Printer.fst"
                                           (Prims.of_int (94))
                                           (Prims.of_int (6))
                                           (Prims.of_int (97))
                                           (Prims.of_int (34)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Syntax.Printer.fst"
                                           (Prims.of_int (94))
                                           (Prims.of_int (6))
                                           (Prims.of_int (97))
                                           (Prims.of_int (34)))))
                                  (Obj.magic uu___2)
                                  (fun uu___3 ->
                                     FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___4 -> uu___3 uu___1))))
                            uu___1)))
           | Pulse_Syntax_Pure.Tm_ExistsSL (uu___, uu___1, uu___2) ->
               Obj.magic
                 (Obj.repr
                    (let uu___3 =
                       Obj.magic
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___4 ->
                               collect_binders
                                 Pulse_Syntax_Pure.uu___is_Tm_ExistsSL t)) in
                     FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                                (Prims.of_int (100)) (Prims.of_int (21))
                                (Prims.of_int (100)) (Prims.of_int (51)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                                (Prims.of_int (99)) (Prims.of_int (26))
                                (Prims.of_int (104)) (Prims.of_int (51)))))
                       (Obj.magic uu___3)
                       (fun uu___4 ->
                          (fun uu___4 ->
                             match uu___4 with
                             | (bs, body) ->
                                 let uu___5 =
                                   term_to_string' (indent level) body in
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Syntax.Printer.fst"
                                               (Prims.of_int (104))
                                               (Prims.of_int (14))
                                               (Prims.of_int (104))
                                               (Prims.of_int (51)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Syntax.Printer.fst"
                                               (Prims.of_int (101))
                                               (Prims.of_int (6))
                                               (Prims.of_int (104))
                                               (Prims.of_int (51)))))
                                      (Obj.magic uu___5)
                                      (fun uu___6 ->
                                         (fun uu___6 ->
                                            let uu___7 =
                                              let uu___8 =
                                                let uu___9 =
                                                  let uu___10 =
                                                    FStar_Tactics_Util.map
                                                      binder_to_string_paren
                                                      bs in
                                                  FStar_Tactics_Effect.tac_bind
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Syntax.Printer.fst"
                                                             (Prims.of_int (102))
                                                             (Prims.of_int (15))
                                                             (Prims.of_int (102))
                                                             (Prims.of_int (46)))))
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Syntax.Printer.fst"
                                                             (Prims.of_int (102))
                                                             (Prims.of_int (14))
                                                             (Prims.of_int (102))
                                                             (Prims.of_int (68)))))
                                                    (Obj.magic uu___10)
                                                    (fun uu___11 ->
                                                       FStar_Tactics_Effect.lift_div_tac
                                                         (fun uu___12 ->
                                                            FStar_String.concat
                                                              " " uu___11)) in
                                                FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Syntax.Printer.fst"
                                                           (Prims.of_int (102))
                                                           (Prims.of_int (14))
                                                           (Prims.of_int (102))
                                                           (Prims.of_int (68)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.Printf.fst"
                                                           (Prims.of_int (122))
                                                           (Prims.of_int (8))
                                                           (Prims.of_int (124))
                                                           (Prims.of_int (44)))))
                                                  (Obj.magic uu___9)
                                                  (fun uu___10 ->
                                                     FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___11 ->
                                                          fun x ->
                                                            fun x1 ->
                                                              Prims.strcat
                                                                (Prims.strcat
                                                                   (Prims.strcat
                                                                    "(exists* "
                                                                    (Prims.strcat
                                                                    uu___10
                                                                    ".\n"))
                                                                   (Prims.strcat
                                                                    x ""))
                                                                (Prims.strcat
                                                                   x1 ")"))) in
                                              FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Syntax.Printer.fst"
                                                         (Prims.of_int (101))
                                                         (Prims.of_int (6))
                                                         (Prims.of_int (104))
                                                         (Prims.of_int (51)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Syntax.Printer.fst"
                                                         (Prims.of_int (101))
                                                         (Prims.of_int (6))
                                                         (Prims.of_int (104))
                                                         (Prims.of_int (51)))))
                                                (Obj.magic uu___8)
                                                (fun uu___9 ->
                                                   FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___10 ->
                                                        uu___9 level)) in
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Syntax.Printer.fst"
                                                          (Prims.of_int (101))
                                                          (Prims.of_int (6))
                                                          (Prims.of_int (104))
                                                          (Prims.of_int (51)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Syntax.Printer.fst"
                                                          (Prims.of_int (101))
                                                          (Prims.of_int (6))
                                                          (Prims.of_int (104))
                                                          (Prims.of_int (51)))))
                                                 (Obj.magic uu___7)
                                                 (fun uu___8 ->
                                                    FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___9 ->
                                                         uu___8 uu___6))))
                                           uu___6))) uu___4)))
           | Pulse_Syntax_Pure.Tm_ForallSL (u, b, body) ->
               Obj.magic
                 (Obj.repr
                    (let uu___ =
                       Obj.magic
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___1 ->
                               collect_binders
                                 Pulse_Syntax_Pure.uu___is_Tm_ForallSL t)) in
                     FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                                (Prims.of_int (107)) (Prims.of_int (21))
                                (Prims.of_int (107)) (Prims.of_int (51)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                                (Prims.of_int (106)) (Prims.of_int (29))
                                (Prims.of_int (111)) (Prims.of_int (51)))))
                       (Obj.magic uu___)
                       (fun uu___1 ->
                          (fun uu___1 ->
                             match uu___1 with
                             | (bs, body1) ->
                                 let uu___2 =
                                   term_to_string' (indent level) body1 in
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Syntax.Printer.fst"
                                               (Prims.of_int (111))
                                               (Prims.of_int (14))
                                               (Prims.of_int (111))
                                               (Prims.of_int (51)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Syntax.Printer.fst"
                                               (Prims.of_int (108))
                                               (Prims.of_int (6))
                                               (Prims.of_int (111))
                                               (Prims.of_int (51)))))
                                      (Obj.magic uu___2)
                                      (fun uu___3 ->
                                         (fun uu___3 ->
                                            let uu___4 =
                                              let uu___5 =
                                                let uu___6 =
                                                  let uu___7 =
                                                    FStar_Tactics_Util.map
                                                      binder_to_string_paren
                                                      bs in
                                                  FStar_Tactics_Effect.tac_bind
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Syntax.Printer.fst"
                                                             (Prims.of_int (109))
                                                             (Prims.of_int (15))
                                                             (Prims.of_int (109))
                                                             (Prims.of_int (46)))))
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Syntax.Printer.fst"
                                                             (Prims.of_int (109))
                                                             (Prims.of_int (14))
                                                             (Prims.of_int (109))
                                                             (Prims.of_int (68)))))
                                                    (Obj.magic uu___7)
                                                    (fun uu___8 ->
                                                       FStar_Tactics_Effect.lift_div_tac
                                                         (fun uu___9 ->
                                                            FStar_String.concat
                                                              " " uu___8)) in
                                                FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Pulse.Syntax.Printer.fst"
                                                           (Prims.of_int (109))
                                                           (Prims.of_int (14))
                                                           (Prims.of_int (109))
                                                           (Prims.of_int (68)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.Printf.fst"
                                                           (Prims.of_int (122))
                                                           (Prims.of_int (8))
                                                           (Prims.of_int (124))
                                                           (Prims.of_int (44)))))
                                                  (Obj.magic uu___6)
                                                  (fun uu___7 ->
                                                     FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___8 ->
                                                          fun x ->
                                                            fun x1 ->
                                                              Prims.strcat
                                                                (Prims.strcat
                                                                   (Prims.strcat
                                                                    "(forall* "
                                                                    (Prims.strcat
                                                                    uu___7
                                                                    ".\n"))
                                                                   (Prims.strcat
                                                                    x ""))
                                                                (Prims.strcat
                                                                   x1 ")"))) in
                                              FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Syntax.Printer.fst"
                                                         (Prims.of_int (108))
                                                         (Prims.of_int (6))
                                                         (Prims.of_int (111))
                                                         (Prims.of_int (51)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Syntax.Printer.fst"
                                                         (Prims.of_int (108))
                                                         (Prims.of_int (6))
                                                         (Prims.of_int (111))
                                                         (Prims.of_int (51)))))
                                                (Obj.magic uu___5)
                                                (fun uu___6 ->
                                                   FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___7 ->
                                                        uu___6 level)) in
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Syntax.Printer.fst"
                                                          (Prims.of_int (108))
                                                          (Prims.of_int (6))
                                                          (Prims.of_int (111))
                                                          (Prims.of_int (51)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Syntax.Printer.fst"
                                                          (Prims.of_int (108))
                                                          (Prims.of_int (6))
                                                          (Prims.of_int (111))
                                                          (Prims.of_int (51)))))
                                                 (Obj.magic uu___4)
                                                 (fun uu___5 ->
                                                    FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___6 ->
                                                         uu___5 uu___3))))
                                           uu___3))) uu___1)))
           | Pulse_Syntax_Pure.Tm_SLProp ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac
                       (fun uu___ -> "slprop")))
           | Pulse_Syntax_Pure.Tm_Inames ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac
                       (fun uu___ -> "inames")))
           | Pulse_Syntax_Pure.Tm_EmpInames ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac
                       (fun uu___ -> "emp_inames")))
           | Pulse_Syntax_Pure.Tm_Unknown ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> "_")))
           | Pulse_Syntax_Pure.Tm_Inv (i, p) ->
               Obj.magic
                 (Obj.repr
                    (let uu___ = term_to_string' level p in
                     FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                                (Prims.of_int (120)) (Prims.of_int (8))
                                (Prims.of_int (120)) (Prims.of_int (33)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                                (Prims.of_int (118)) (Prims.of_int (6))
                                (Prims.of_int (120)) (Prims.of_int (33)))))
                       (Obj.magic uu___)
                       (fun uu___1 ->
                          (fun uu___1 ->
                             let uu___2 =
                               let uu___3 = term_to_string' level i in
                               FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Syntax.Printer.fst"
                                          (Prims.of_int (119))
                                          (Prims.of_int (8))
                                          (Prims.of_int (119))
                                          (Prims.of_int (33)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "FStar.Printf.fst"
                                          (Prims.of_int (122))
                                          (Prims.of_int (8))
                                          (Prims.of_int (124))
                                          (Prims.of_int (44)))))
                                 (Obj.magic uu___3)
                                 (fun uu___4 ->
                                    FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___5 ->
                                         fun x ->
                                           Prims.strcat
                                             (Prims.strcat "inv "
                                                (Prims.strcat uu___4 " "))
                                             (Prims.strcat x ""))) in
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Syntax.Printer.fst"
                                           (Prims.of_int (118))
                                           (Prims.of_int (6))
                                           (Prims.of_int (120))
                                           (Prims.of_int (33)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Syntax.Printer.fst"
                                           (Prims.of_int (118))
                                           (Prims.of_int (6))
                                           (Prims.of_int (120))
                                           (Prims.of_int (33)))))
                                  (Obj.magic uu___2)
                                  (fun uu___3 ->
                                     FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___4 -> uu___3 uu___1))))
                            uu___1)))
           | Pulse_Syntax_Pure.Tm_FStar t1 ->
               Obj.magic
                 (Obj.repr (FStar_Tactics_V2_Builtins.term_to_string t1)))
        uu___1 uu___
let (term_to_string :
  Pulse_Syntax_Base.term ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  = fun t -> term_to_string' "" t
let (star_doc : FStar_Pprint.document) = FStar_Pprint.doc_of_string "**"
let rec fold_right1 :
  'a .
    ('a -> 'a -> ('a, unit) FStar_Tactics_Effect.tac_repr) ->
      'a Prims.list -> ('a, unit) FStar_Tactics_Effect.tac_repr
  =
  fun uu___1 ->
    fun uu___ ->
      (fun f ->
         fun l ->
           match l with
           | [] ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_V2_Derived.fail "fold_right1: empty list"))
           | x::[] ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> x)))
           | hd::tl ->
               Obj.magic
                 (Obj.repr
                    (let uu___ = fold_right1 f tl in
                     FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                                (Prims.of_int (131)) (Prims.of_int (19))
                                (Prims.of_int (131)) (Prims.of_int (37)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                                (Prims.of_int (131)) (Prims.of_int (14))
                                (Prims.of_int (131)) (Prims.of_int (37)))))
                       (Obj.magic uu___)
                       (fun uu___1 ->
                          (fun uu___1 -> Obj.magic (f hd uu___1)) uu___1))))
        uu___1 uu___
let (should_paren_term :
  Pulse_Syntax_Base.term -> (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    let uu___ = FStar_Tactics_NamedView.inspect t in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
               (Prims.of_int (133)) (Prims.of_int (23)) (Prims.of_int (133))
               (Prims.of_int (24)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
               (Prims.of_int (134)) (Prims.of_int (2)) (Prims.of_int (136))
               (Prims.of_int (14))))) (Obj.magic uu___)
      (fun uu___1 ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___2 ->
              match uu___1 with
              | FStar_Tactics_NamedView.Tv_Match (uu___3, uu___4, uu___5) ->
                  true
              | uu___3 -> false))
let rec (binder_to_doc :
  Pulse_Syntax_Base.binder ->
    (FStar_Pprint.document, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun b ->
    let uu___ =
      let uu___1 =
        let uu___2 =
          FStar_Tactics_Unseal.unseal
            (b.Pulse_Syntax_Base.binder_ppname).Pulse_Syntax_Base.name in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                   (Prims.of_int (139)) (Prims.of_int (24))
                   (Prims.of_int (139)) (Prims.of_int (55)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                   (Prims.of_int (139)) (Prims.of_int (10))
                   (Prims.of_int (139)) (Prims.of_int (55)))))
          (Obj.magic uu___2)
          (fun uu___3 ->
             FStar_Tactics_Effect.lift_div_tac
               (fun uu___4 -> FStar_Pprint.doc_of_string uu___3)) in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                 (Prims.of_int (139)) (Prims.of_int (10))
                 (Prims.of_int (139)) (Prims.of_int (55)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                 (Prims.of_int (139)) (Prims.of_int (9)) (Prims.of_int (141))
                 (Prims.of_int (37))))) (Obj.magic uu___1)
        (fun uu___2 ->
           (fun uu___2 ->
              let uu___3 =
                let uu___4 = term_to_doc b.Pulse_Syntax_Base.binder_ty in
                FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                           (Prims.of_int (141)) (Prims.of_int (13))
                           (Prims.of_int (141)) (Prims.of_int (36)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                           (Prims.of_int (140)) (Prims.of_int (13))
                           (Prims.of_int (141)) (Prims.of_int (36)))))
                  (Obj.magic uu___4)
                  (fun uu___5 ->
                     FStar_Tactics_Effect.lift_div_tac
                       (fun uu___6 ->
                          FStar_Pprint.op_Hat_Hat
                            (FStar_Pprint.doc_of_string ":") uu___5)) in
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                            (Prims.of_int (140)) (Prims.of_int (13))
                            (Prims.of_int (141)) (Prims.of_int (36)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                            (Prims.of_int (139)) (Prims.of_int (9))
                            (Prims.of_int (141)) (Prims.of_int (37)))))
                   (Obj.magic uu___3)
                   (fun uu___4 ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___5 -> FStar_Pprint.op_Hat_Hat uu___2 uu___4))))
             uu___2) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
               (Prims.of_int (139)) (Prims.of_int (9)) (Prims.of_int (141))
               (Prims.of_int (37)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
               (Prims.of_int (139)) (Prims.of_int (2)) (Prims.of_int (141))
               (Prims.of_int (37))))) (Obj.magic uu___)
      (fun uu___1 ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___2 -> FStar_Pprint.parens uu___1))
and (term_to_doc :
  Pulse_Syntax_Base.term ->
    (FStar_Pprint.document, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    (fun t ->
       match Pulse_Syntax_Pure.inspect_term t with
       | Pulse_Syntax_Pure.Tm_Emp ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___ -> FStar_Pprint.doc_of_string "emp")))
       | Pulse_Syntax_Pure.Tm_Pure p ->
           Obj.magic
             (Obj.repr
                (let uu___ =
                   let uu___1 = term_to_doc p in
                   FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                              (Prims.of_int (147)) (Prims.of_int (51))
                              (Prims.of_int (147)) (Prims.of_int (66)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                              (Prims.of_int (147)) (Prims.of_int (44))
                              (Prims.of_int (147)) (Prims.of_int (66)))))
                     (Obj.magic uu___1)
                     (fun uu___2 ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___3 -> FStar_Pprint.parens uu___2)) in
                 FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                            (Prims.of_int (147)) (Prims.of_int (44))
                            (Prims.of_int (147)) (Prims.of_int (66)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                            (Prims.of_int (147)) (Prims.of_int (19))
                            (Prims.of_int (147)) (Prims.of_int (66)))))
                   (Obj.magic uu___)
                   (fun uu___1 ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___2 ->
                           FStar_Pprint.op_Hat_Hat
                             (FStar_Pprint.doc_of_string "pure ") uu___1))))
       | Pulse_Syntax_Pure.Tm_Star (uu___, uu___1) ->
           Obj.magic
             (Obj.repr
                (let uu___2 =
                   Obj.magic
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___3 -> Pulse_Syntax_Pure.slprop_as_list t)) in
                 FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                            (Prims.of_int (158)) (Prims.of_int (23))
                            (Prims.of_int (158)) (Prims.of_int (39)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                            (Prims.of_int (158)) (Prims.of_int (42))
                            (Prims.of_int (169)) (Prims.of_int (80)))))
                   (Obj.magic uu___2)
                   (fun uu___3 ->
                      (fun components ->
                         let uu___3 =
                           Obj.magic
                             (FStar_Tactics_Effect.lift_div_tac
                                (fun uu___4 ->
                                   fun t1 ->
                                     let uu___5 = should_paren_term t1 in
                                     FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Syntax.Printer.fst"
                                                (Prims.of_int (160))
                                                (Prims.of_int (11))
                                                (Prims.of_int (160))
                                                (Prims.of_int (30)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Syntax.Printer.fst"
                                                (Prims.of_int (160))
                                                (Prims.of_int (8))
                                                (Prims.of_int (162))
                                                (Prims.of_int (26)))))
                                       (Obj.magic uu___5)
                                       (fun uu___6 ->
                                          (fun uu___6 ->
                                             if uu___6
                                             then
                                               let uu___7 = term_to_doc t1 in
                                               Obj.magic
                                                 (FStar_Tactics_Effect.tac_bind
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Syntax.Printer.fst"
                                                             (Prims.of_int (161))
                                                             (Prims.of_int (20))
                                                             (Prims.of_int (161))
                                                             (Prims.of_int (35)))))
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Syntax.Printer.fst"
                                                             (Prims.of_int (161))
                                                             (Prims.of_int (13))
                                                             (Prims.of_int (161))
                                                             (Prims.of_int (35)))))
                                                    (Obj.magic uu___7)
                                                    (fun uu___8 ->
                                                       FStar_Tactics_Effect.lift_div_tac
                                                         (fun uu___9 ->
                                                            FStar_Pprint.parens
                                                              uu___8)))
                                             else Obj.magic (term_to_doc t1))
                                            uu___6))) in
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Syntax.Printer.fst"
                                       (Prims.of_int (160))
                                       (Prims.of_int (8))
                                       (Prims.of_int (162))
                                       (Prims.of_int (26)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Syntax.Printer.fst"
                                       (Prims.of_int (163))
                                       (Prims.of_int (8))
                                       (Prims.of_int (169))
                                       (Prims.of_int (80)))))
                              (Obj.magic uu___3)
                              (fun uu___4 ->
                                 (fun term_to_doc_paren ->
                                    let uu___4 =
                                      FStar_Tactics_Util.map
                                        term_to_doc_paren components in
                                    Obj.magic
                                      (FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Syntax.Printer.fst"
                                                  (Prims.of_int (164))
                                                  (Prims.of_int (17))
                                                  (Prims.of_int (164))
                                                  (Prims.of_int (51)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Syntax.Printer.fst"
                                                  (Prims.of_int (168))
                                                  (Prims.of_int (6))
                                                  (Prims.of_int (169))
                                                  (Prims.of_int (80)))))
                                         (Obj.magic uu___4)
                                         (fun uu___5 ->
                                            (fun docs ->
                                               let uu___5 =
                                                 fold_right1
                                                   (fun uu___7 ->
                                                      fun uu___6 ->
                                                        (fun p ->
                                                           fun q ->
                                                             Obj.magic
                                                               (FStar_Tactics_Effect.lift_div_tac
                                                                  (fun uu___6
                                                                    ->
                                                                    FStar_Pprint.op_Hat_Slash_Hat
                                                                    (FStar_Pprint.op_Hat_Hat
                                                                    p
                                                                    (FStar_Pprint.op_Hat_Hat
                                                                    (FStar_Pprint.doc_of_string
                                                                    " ")
                                                                    star_doc))
                                                                    q)))
                                                          uu___7 uu___6) docs in
                                               Obj.magic
                                                 (FStar_Tactics_Effect.tac_bind
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Syntax.Printer.fst"
                                                             (Prims.of_int (169))
                                                             (Prims.of_int (8))
                                                             (Prims.of_int (169))
                                                             (Prims.of_int (80)))))
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Syntax.Printer.fst"
                                                             (Prims.of_int (168))
                                                             (Prims.of_int (6))
                                                             (Prims.of_int (169))
                                                             (Prims.of_int (80)))))
                                                    (Obj.magic uu___5)
                                                    (fun uu___6 ->
                                                       FStar_Tactics_Effect.lift_div_tac
                                                         (fun uu___7 ->
                                                            FStar_Pprint.group
                                                              uu___6))))
                                              uu___5))) uu___4))) uu___3)))
       | Pulse_Syntax_Pure.Tm_ExistsSL (uu___, uu___1, uu___2) ->
           Obj.magic
             (Obj.repr
                (let uu___3 =
                   Obj.magic
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___4 ->
                           collect_binders
                             Pulse_Syntax_Pure.uu___is_Tm_ExistsSL t)) in
                 FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                            (Prims.of_int (172)) (Prims.of_int (21))
                            (Prims.of_int (172)) (Prims.of_int (51)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                            (Prims.of_int (171)) (Prims.of_int (26))
                            (Prims.of_int (176)) (Prims.of_int (37)))))
                   (Obj.magic uu___3)
                   (fun uu___4 ->
                      (fun uu___4 ->
                         match uu___4 with
                         | (bs, body) ->
                             let uu___5 =
                               let uu___6 =
                                 let uu___7 =
                                   let uu___8 =
                                     FStar_Tactics_Util.map binder_to_doc bs in
                                   FStar_Tactics_Effect.tac_bind
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Syntax.Printer.fst"
                                              (Prims.of_int (173))
                                              (Prims.of_int (62))
                                              (Prims.of_int (173))
                                              (Prims.of_int (86)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Syntax.Printer.fst"
                                              (Prims.of_int (173))
                                              (Prims.of_int (32))
                                              (Prims.of_int (173))
                                              (Prims.of_int (87)))))
                                     (Obj.magic uu___8)
                                     (fun uu___9 ->
                                        FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___10 ->
                                             FStar_Pprint.separate
                                               (FStar_Pprint.doc_of_string
                                                  " ") uu___9)) in
                                 FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Syntax.Printer.fst"
                                            (Prims.of_int (173))
                                            (Prims.of_int (32))
                                            (Prims.of_int (173))
                                            (Prims.of_int (87)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Syntax.Printer.fst"
                                            (Prims.of_int (173))
                                            (Prims.of_int (25))
                                            (Prims.of_int (173))
                                            (Prims.of_int (88)))))
                                   (Obj.magic uu___7)
                                   (fun uu___8 ->
                                      FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___9 ->
                                           FStar_Pprint.group uu___8)) in
                               FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Syntax.Printer.fst"
                                          (Prims.of_int (173))
                                          (Prims.of_int (25))
                                          (Prims.of_int (173))
                                          (Prims.of_int (88)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Syntax.Printer.fst"
                                          (Prims.of_int (173))
                                          (Prims.of_int (19))
                                          (Prims.of_int (173))
                                          (Prims.of_int (88)))))
                                 (Obj.magic uu___6)
                                 (fun uu___7 ->
                                    FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___8 ->
                                         FStar_Pprint.align uu___7)) in
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Syntax.Printer.fst"
                                           (Prims.of_int (173))
                                           (Prims.of_int (19))
                                           (Prims.of_int (173))
                                           (Prims.of_int (88)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Syntax.Printer.fst"
                                           (Prims.of_int (174))
                                           (Prims.of_int (6))
                                           (Prims.of_int (176))
                                           (Prims.of_int (37)))))
                                  (Obj.magic uu___5)
                                  (fun uu___6 ->
                                     (fun bs_doc ->
                                        let uu___6 =
                                          let uu___7 = term_to_doc body in
                                          FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Syntax.Printer.fst"
                                                     (Prims.of_int (176))
                                                     (Prims.of_int (19))
                                                     (Prims.of_int (176))
                                                     (Prims.of_int (37)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Syntax.Printer.fst"
                                                     (Prims.of_int (175))
                                                     (Prims.of_int (8))
                                                     (Prims.of_int (176))
                                                     (Prims.of_int (37)))))
                                            (Obj.magic uu___7)
                                            (fun uu___8 ->
                                               FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___9 ->
                                                    FStar_Pprint.prefix
                                                      (Prims.of_int (2))
                                                      Prims.int_one
                                                      (FStar_Pprint.op_Hat_Hat
                                                         (FStar_Pprint.prefix
                                                            (Prims.of_int (2))
                                                            Prims.int_one
                                                            (FStar_Pprint.doc_of_string
                                                               "exists*")
                                                            bs_doc)
                                                         FStar_Pprint.dot)
                                                      uu___8)) in
                                        Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Syntax.Printer.fst"
                                                      (Prims.of_int (175))
                                                      (Prims.of_int (8))
                                                      (Prims.of_int (176))
                                                      (Prims.of_int (37)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Syntax.Printer.fst"
                                                      (Prims.of_int (174))
                                                      (Prims.of_int (6))
                                                      (Prims.of_int (176))
                                                      (Prims.of_int (37)))))
                                             (Obj.magic uu___6)
                                             (fun uu___7 ->
                                                FStar_Tactics_Effect.lift_div_tac
                                                  (fun uu___8 ->
                                                     FStar_Pprint.parens
                                                       uu___7)))) uu___6)))
                        uu___4)))
       | Pulse_Syntax_Pure.Tm_ForallSL (uu___, uu___1, uu___2) ->
           Obj.magic
             (Obj.repr
                (let uu___3 =
                   Obj.magic
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___4 ->
                           collect_binders
                             Pulse_Syntax_Pure.uu___is_Tm_ForallSL t)) in
                 FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                            (Prims.of_int (182)) (Prims.of_int (21))
                            (Prims.of_int (182)) (Prims.of_int (51)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                            (Prims.of_int (181)) (Prims.of_int (26))
                            (Prims.of_int (186)) (Prims.of_int (37)))))
                   (Obj.magic uu___3)
                   (fun uu___4 ->
                      (fun uu___4 ->
                         match uu___4 with
                         | (bs, body) ->
                             let uu___5 =
                               let uu___6 =
                                 let uu___7 =
                                   let uu___8 =
                                     FStar_Tactics_Util.map binder_to_doc bs in
                                   FStar_Tactics_Effect.tac_bind
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Syntax.Printer.fst"
                                              (Prims.of_int (183))
                                              (Prims.of_int (62))
                                              (Prims.of_int (183))
                                              (Prims.of_int (86)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "Pulse.Syntax.Printer.fst"
                                              (Prims.of_int (183))
                                              (Prims.of_int (32))
                                              (Prims.of_int (183))
                                              (Prims.of_int (87)))))
                                     (Obj.magic uu___8)
                                     (fun uu___9 ->
                                        FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___10 ->
                                             FStar_Pprint.separate
                                               (FStar_Pprint.doc_of_string
                                                  " ") uu___9)) in
                                 FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Syntax.Printer.fst"
                                            (Prims.of_int (183))
                                            (Prims.of_int (32))
                                            (Prims.of_int (183))
                                            (Prims.of_int (87)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Syntax.Printer.fst"
                                            (Prims.of_int (183))
                                            (Prims.of_int (25))
                                            (Prims.of_int (183))
                                            (Prims.of_int (88)))))
                                   (Obj.magic uu___7)
                                   (fun uu___8 ->
                                      FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___9 ->
                                           FStar_Pprint.group uu___8)) in
                               FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Syntax.Printer.fst"
                                          (Prims.of_int (183))
                                          (Prims.of_int (25))
                                          (Prims.of_int (183))
                                          (Prims.of_int (88)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Syntax.Printer.fst"
                                          (Prims.of_int (183))
                                          (Prims.of_int (19))
                                          (Prims.of_int (183))
                                          (Prims.of_int (88)))))
                                 (Obj.magic uu___6)
                                 (fun uu___7 ->
                                    FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___8 ->
                                         FStar_Pprint.align uu___7)) in
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Syntax.Printer.fst"
                                           (Prims.of_int (183))
                                           (Prims.of_int (19))
                                           (Prims.of_int (183))
                                           (Prims.of_int (88)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Syntax.Printer.fst"
                                           (Prims.of_int (184))
                                           (Prims.of_int (6))
                                           (Prims.of_int (186))
                                           (Prims.of_int (37)))))
                                  (Obj.magic uu___5)
                                  (fun uu___6 ->
                                     (fun bs_doc ->
                                        let uu___6 =
                                          let uu___7 = term_to_doc body in
                                          FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Syntax.Printer.fst"
                                                     (Prims.of_int (186))
                                                     (Prims.of_int (19))
                                                     (Prims.of_int (186))
                                                     (Prims.of_int (37)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Syntax.Printer.fst"
                                                     (Prims.of_int (185))
                                                     (Prims.of_int (8))
                                                     (Prims.of_int (186))
                                                     (Prims.of_int (37)))))
                                            (Obj.magic uu___7)
                                            (fun uu___8 ->
                                               FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___9 ->
                                                    FStar_Pprint.prefix
                                                      (Prims.of_int (2))
                                                      Prims.int_one
                                                      (FStar_Pprint.op_Hat_Hat
                                                         (FStar_Pprint.prefix
                                                            (Prims.of_int (2))
                                                            Prims.int_one
                                                            (FStar_Pprint.doc_of_string
                                                               "forall*")
                                                            bs_doc)
                                                         FStar_Pprint.dot)
                                                      uu___8)) in
                                        Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Syntax.Printer.fst"
                                                      (Prims.of_int (185))
                                                      (Prims.of_int (8))
                                                      (Prims.of_int (186))
                                                      (Prims.of_int (37)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Syntax.Printer.fst"
                                                      (Prims.of_int (184))
                                                      (Prims.of_int (6))
                                                      (Prims.of_int (186))
                                                      (Prims.of_int (37)))))
                                             (Obj.magic uu___6)
                                             (fun uu___7 ->
                                                FStar_Tactics_Effect.lift_div_tac
                                                  (fun uu___8 ->
                                                     FStar_Pprint.parens
                                                       uu___7)))) uu___6)))
                        uu___4)))
       | Pulse_Syntax_Pure.Tm_SLProp ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___ -> FStar_Pprint.doc_of_string "slprop")))
       | Pulse_Syntax_Pure.Tm_Inames ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___ -> FStar_Pprint.doc_of_string "inames")))
       | Pulse_Syntax_Pure.Tm_EmpInames ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___ -> FStar_Pprint.doc_of_string "emp_inames")))
       | Pulse_Syntax_Pure.Tm_Inv (i, p) ->
           Obj.magic
             (Obj.repr
                (let uu___ =
                   let uu___1 = term_to_doc i in
                   FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                              (Prims.of_int (193)) (Prims.of_int (8))
                              (Prims.of_int (193)) (Prims.of_int (21)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                              (Prims.of_int (193)) (Prims.of_int (8))
                              (Prims.of_int (195)) (Prims.of_int (30)))))
                     (Obj.magic uu___1)
                     (fun uu___2 ->
                        (fun uu___2 ->
                           let uu___3 =
                             let uu___4 =
                               let uu___5 = term_to_doc p in
                               FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Syntax.Printer.fst"
                                          (Prims.of_int (195))
                                          (Prims.of_int (15))
                                          (Prims.of_int (195))
                                          (Prims.of_int (30)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Syntax.Printer.fst"
                                          (Prims.of_int (195))
                                          (Prims.of_int (8))
                                          (Prims.of_int (195))
                                          (Prims.of_int (30)))))
                                 (Obj.magic uu___5)
                                 (fun uu___6 ->
                                    FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___7 ->
                                         FStar_Pprint.parens uu___6)) in
                             FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Syntax.Printer.fst"
                                        (Prims.of_int (195))
                                        (Prims.of_int (8))
                                        (Prims.of_int (195))
                                        (Prims.of_int (30)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Syntax.Printer.fst"
                                        (Prims.of_int (194))
                                        (Prims.of_int (8))
                                        (Prims.of_int (195))
                                        (Prims.of_int (30)))))
                               (Obj.magic uu___4)
                               (fun uu___5 ->
                                  FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___6 ->
                                       FStar_Pprint.op_Hat_Hat
                                         (FStar_Pprint.doc_of_string " ")
                                         uu___5)) in
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Syntax.Printer.fst"
                                         (Prims.of_int (194))
                                         (Prims.of_int (8))
                                         (Prims.of_int (195))
                                         (Prims.of_int (30)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Syntax.Printer.fst"
                                         (Prims.of_int (193))
                                         (Prims.of_int (8))
                                         (Prims.of_int (195))
                                         (Prims.of_int (30)))))
                                (Obj.magic uu___3)
                                (fun uu___4 ->
                                   FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___5 ->
                                        FStar_Pprint.op_Hat_Hat uu___2 uu___4))))
                          uu___2) in
                 FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                            (Prims.of_int (193)) (Prims.of_int (8))
                            (Prims.of_int (195)) (Prims.of_int (30)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                            (Prims.of_int (192)) (Prims.of_int (6))
                            (Prims.of_int (195)) (Prims.of_int (30)))))
                   (Obj.magic uu___)
                   (fun uu___1 ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___2 ->
                           FStar_Pprint.op_Hat_Hat
                             (FStar_Pprint.doc_of_string "inv ") uu___1))))
       | Pulse_Syntax_Pure.Tm_Unknown ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___ -> FStar_Pprint.doc_of_string "_")))
       | Pulse_Syntax_Pure.Tm_FStar t1 ->
           Obj.magic (Obj.repr (FStar_Tactics_V2_Builtins.term_to_doc t1)))
      uu___
let (binder_to_string :
  Pulse_Syntax_Base.binder ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun b ->
    let uu___ = term_to_string b.Pulse_Syntax_Base.binder_ty in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
               (Prims.of_int (207)) (Prims.of_int (12)) (Prims.of_int (207))
               (Prims.of_int (40)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
               (Prims.of_int (202)) (Prims.of_int (4)) (Prims.of_int (207))
               (Prims.of_int (40))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun uu___1 ->
            let uu___2 =
              let uu___3 =
                FStar_Tactics_Unseal.unseal
                  (b.Pulse_Syntax_Base.binder_ppname).Pulse_Syntax_Base.name in
              FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                         (Prims.of_int (206)) (Prims.of_int (12))
                         (Prims.of_int (206)) (Prims.of_int (43)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                         (Prims.of_int (202)) (Prims.of_int (4))
                         (Prims.of_int (207)) (Prims.of_int (40)))))
                (Obj.magic uu___3)
                (fun uu___4 ->
                   (fun uu___4 ->
                      let uu___5 =
                        let uu___6 =
                          let uu___7 =
                            FStar_Tactics_Unseal.unseal
                              b.Pulse_Syntax_Base.binder_attrs in
                          FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "Pulse.Syntax.Printer.fst"
                                     (Prims.of_int (203)) (Prims.of_int (19))
                                     (Prims.of_int (203)) (Prims.of_int (42)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "Pulse.Syntax.Printer.fst"
                                     (Prims.of_int (203)) (Prims.of_int (12))
                                     (Prims.of_int (205)) (Prims.of_int (91)))))
                            (Obj.magic uu___7)
                            (fun uu___8 ->
                               (fun uu___8 ->
                                  match uu___8 with
                                  | [] ->
                                      Obj.magic
                                        (Obj.repr
                                           (FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___9 -> "")))
                                  | l ->
                                      Obj.magic
                                        (Obj.repr
                                           (let uu___9 =
                                              let uu___10 =
                                                FStar_Tactics_Util.map
                                                  (term_to_string' "") l in
                                              FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Syntax.Printer.fst"
                                                         (Prims.of_int (205))
                                                         (Prims.of_int (59))
                                                         (Prims.of_int (205))
                                                         (Prims.of_int (89)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "Pulse.Syntax.Printer.fst"
                                                         (Prims.of_int (205))
                                                         (Prims.of_int (40))
                                                         (Prims.of_int (205))
                                                         (Prims.of_int (90)))))
                                                (Obj.magic uu___10)
                                                (fun uu___11 ->
                                                   FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___12 ->
                                                        FStar_String.concat
                                                          ";" uu___11)) in
                                            FStar_Tactics_Effect.tac_bind
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Syntax.Printer.fst"
                                                       (Prims.of_int (205))
                                                       (Prims.of_int (40))
                                                       (Prims.of_int (205))
                                                       (Prims.of_int (90)))))
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
                                                      Prims.strcat "[@@@ "
                                                        (Prims.strcat uu___10
                                                           "] ")))))) uu___8) in
                        FStar_Tactics_Effect.tac_bind
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "Pulse.Syntax.Printer.fst"
                                   (Prims.of_int (203)) (Prims.of_int (12))
                                   (Prims.of_int (205)) (Prims.of_int (91)))))
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range "FStar.Printf.fst"
                                   (Prims.of_int (122)) (Prims.of_int (8))
                                   (Prims.of_int (124)) (Prims.of_int (44)))))
                          (Obj.magic uu___6)
                          (fun uu___7 ->
                             FStar_Tactics_Effect.lift_div_tac
                               (fun uu___8 ->
                                  fun x ->
                                    fun x1 ->
                                      Prims.strcat
                                        (Prims.strcat
                                           (Prims.strcat ""
                                              (Prims.strcat uu___7 ""))
                                           (Prims.strcat x ":"))
                                        (Prims.strcat x1 ""))) in
                      Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Syntax.Printer.fst"
                                    (Prims.of_int (202)) (Prims.of_int (4))
                                    (Prims.of_int (207)) (Prims.of_int (40)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Pulse.Syntax.Printer.fst"
                                    (Prims.of_int (202)) (Prims.of_int (4))
                                    (Prims.of_int (207)) (Prims.of_int (40)))))
                           (Obj.magic uu___5)
                           (fun uu___6 ->
                              FStar_Tactics_Effect.lift_div_tac
                                (fun uu___7 -> uu___6 uu___4)))) uu___4) in
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                          (Prims.of_int (202)) (Prims.of_int (4))
                          (Prims.of_int (207)) (Prims.of_int (40)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                          (Prims.of_int (202)) (Prims.of_int (4))
                          (Prims.of_int (207)) (Prims.of_int (40)))))
                 (Obj.magic uu___2)
                 (fun uu___3 ->
                    FStar_Tactics_Effect.lift_div_tac
                      (fun uu___4 -> uu___3 uu___1)))) uu___1)
let (ctag_to_string : Pulse_Syntax_Base.ctag -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | Pulse_Syntax_Base.STT -> "ST"
    | Pulse_Syntax_Base.STT_Atomic -> "STAtomic"
    | Pulse_Syntax_Base.STT_Ghost -> "STGhost"
let (observability_to_string :
  Pulse_Syntax_Base.observability -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | Pulse_Syntax_Base.Observable -> "Observable"
    | Pulse_Syntax_Base.Neutral -> "Neutral"
let (effect_annot_to_string :
  Pulse_Syntax_Base.effect_annot ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    (fun uu___ ->
       match uu___ with
       | Pulse_Syntax_Base.EffectAnnotSTT ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> "stt")))
       | Pulse_Syntax_Base.EffectAnnotGhost
           { Pulse_Syntax_Base.opens = opens;_} ->
           Obj.magic
             (Obj.repr
                (let uu___1 = term_to_string opens in
                 FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                            (Prims.of_int (221)) (Prims.of_int (57))
                            (Prims.of_int (221)) (Prims.of_int (79)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Prims.fst"
                            (Prims.of_int (611)) (Prims.of_int (19))
                            (Prims.of_int (611)) (Prims.of_int (31)))))
                   (Obj.magic uu___1)
                   (fun uu___2 ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___3 ->
                           Prims.strcat "stt_ghost " (Prims.strcat uu___2 "")))))
       | Pulse_Syntax_Base.EffectAnnotAtomic
           { Pulse_Syntax_Base.opens1 = opens;_} ->
           Obj.magic
             (Obj.repr
                (let uu___1 = term_to_string opens in
                 FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                            (Prims.of_int (222)) (Prims.of_int (59))
                            (Prims.of_int (222)) (Prims.of_int (81)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Prims.fst"
                            (Prims.of_int (611)) (Prims.of_int (19))
                            (Prims.of_int (611)) (Prims.of_int (31)))))
                   (Obj.magic uu___1)
                   (fun uu___2 ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___3 ->
                           Prims.strcat "stt_atomic "
                             (Prims.strcat uu___2 "")))))
       | Pulse_Syntax_Base.EffectAnnotAtomicOrGhost
           { Pulse_Syntax_Base.opens2 = opens;_} ->
           Obj.magic
             (Obj.repr
                (let uu___1 = term_to_string opens in
                 FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                            (Prims.of_int (223)) (Prims.of_int (75))
                            (Prims.of_int (223)) (Prims.of_int (97)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Prims.fst"
                            (Prims.of_int (611)) (Prims.of_int (19))
                            (Prims.of_int (611)) (Prims.of_int (31)))))
                   (Obj.magic uu___1)
                   (fun uu___2 ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___3 ->
                           Prims.strcat "stt_atomic_or_ghost "
                             (Prims.strcat uu___2 "")))))) uu___
let (comp_to_string :
  Pulse_Syntax_Base.comp ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun c ->
    match c with
    | Pulse_Syntax_Base.C_Tot t ->
        let uu___ = term_to_string t in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                   (Prims.of_int (229)) (Prims.of_int (23))
                   (Prims.of_int (229)) (Prims.of_int (41)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Prims.fst" (Prims.of_int (611))
                   (Prims.of_int (19)) (Prims.of_int (611))
                   (Prims.of_int (31))))) (Obj.magic uu___)
          (fun uu___1 ->
             FStar_Tactics_Effect.lift_div_tac
               (fun uu___2 -> Prims.strcat "Tot " (Prims.strcat uu___1 "")))
    | Pulse_Syntax_Base.C_ST s ->
        let uu___ = term_to_string s.Pulse_Syntax_Base.post in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                   (Prims.of_int (235)) (Prims.of_int (14))
                   (Prims.of_int (235)) (Prims.of_int (37)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                   (Prims.of_int (232)) (Prims.of_int (6))
                   (Prims.of_int (235)) (Prims.of_int (37)))))
          (Obj.magic uu___)
          (fun uu___1 ->
             (fun uu___1 ->
                let uu___2 =
                  let uu___3 = term_to_string s.Pulse_Syntax_Base.pre in
                  FStar_Tactics_Effect.tac_bind
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                             (Prims.of_int (234)) (Prims.of_int (14))
                             (Prims.of_int (234)) (Prims.of_int (36)))))
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                             (Prims.of_int (232)) (Prims.of_int (6))
                             (Prims.of_int (235)) (Prims.of_int (37)))))
                    (Obj.magic uu___3)
                    (fun uu___4 ->
                       (fun uu___4 ->
                          let uu___5 =
                            let uu___6 =
                              term_to_string s.Pulse_Syntax_Base.res in
                            FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Syntax.Printer.fst"
                                       (Prims.of_int (233))
                                       (Prims.of_int (14))
                                       (Prims.of_int (233))
                                       (Prims.of_int (36)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range "FStar.Printf.fst"
                                       (Prims.of_int (122))
                                       (Prims.of_int (8))
                                       (Prims.of_int (124))
                                       (Prims.of_int (44)))))
                              (Obj.magic uu___6)
                              (fun uu___7 ->
                                 FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___8 ->
                                      fun x ->
                                        fun x1 ->
                                          Prims.strcat
                                            (Prims.strcat
                                               (Prims.strcat "stt "
                                                  (Prims.strcat uu___7
                                                     " (requires\n"))
                                               (Prims.strcat x ") (ensures\n"))
                                            (Prims.strcat x1 ")"))) in
                          Obj.magic
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Syntax.Printer.fst"
                                        (Prims.of_int (232))
                                        (Prims.of_int (6))
                                        (Prims.of_int (235))
                                        (Prims.of_int (37)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Syntax.Printer.fst"
                                        (Prims.of_int (232))
                                        (Prims.of_int (6))
                                        (Prims.of_int (235))
                                        (Prims.of_int (37)))))
                               (Obj.magic uu___5)
                               (fun uu___6 ->
                                  FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___7 -> uu___6 uu___4)))) uu___4) in
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                              (Prims.of_int (232)) (Prims.of_int (6))
                              (Prims.of_int (235)) (Prims.of_int (37)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                              (Prims.of_int (232)) (Prims.of_int (6))
                              (Prims.of_int (235)) (Prims.of_int (37)))))
                     (Obj.magic uu___2)
                     (fun uu___3 ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___4 -> uu___3 uu___1)))) uu___1)
    | Pulse_Syntax_Base.C_STAtomic (inames, obs, s) ->
        let uu___ = term_to_string s.Pulse_Syntax_Base.post in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                   (Prims.of_int (243)) (Prims.of_int (14))
                   (Prims.of_int (243)) (Prims.of_int (37)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                   (Prims.of_int (238)) (Prims.of_int (6))
                   (Prims.of_int (243)) (Prims.of_int (37)))))
          (Obj.magic uu___)
          (fun uu___1 ->
             (fun uu___1 ->
                let uu___2 =
                  let uu___3 = term_to_string s.Pulse_Syntax_Base.pre in
                  FStar_Tactics_Effect.tac_bind
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                             (Prims.of_int (242)) (Prims.of_int (14))
                             (Prims.of_int (242)) (Prims.of_int (36)))))
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                             (Prims.of_int (238)) (Prims.of_int (6))
                             (Prims.of_int (243)) (Prims.of_int (37)))))
                    (Obj.magic uu___3)
                    (fun uu___4 ->
                       (fun uu___4 ->
                          let uu___5 =
                            let uu___6 = term_to_string inames in
                            FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Syntax.Printer.fst"
                                       (Prims.of_int (241))
                                       (Prims.of_int (14))
                                       (Prims.of_int (241))
                                       (Prims.of_int (37)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Syntax.Printer.fst"
                                       (Prims.of_int (238))
                                       (Prims.of_int (6))
                                       (Prims.of_int (243))
                                       (Prims.of_int (37)))))
                              (Obj.magic uu___6)
                              (fun uu___7 ->
                                 (fun uu___7 ->
                                    let uu___8 =
                                      let uu___9 =
                                        let uu___10 =
                                          term_to_string
                                            s.Pulse_Syntax_Base.res in
                                        FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Syntax.Printer.fst"
                                                   (Prims.of_int (239))
                                                   (Prims.of_int (14))
                                                   (Prims.of_int (239))
                                                   (Prims.of_int (36)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "FStar.Printf.fst"
                                                   (Prims.of_int (122))
                                                   (Prims.of_int (8))
                                                   (Prims.of_int (124))
                                                   (Prims.of_int (44)))))
                                          (Obj.magic uu___10)
                                          (fun uu___11 ->
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___12 ->
                                                  fun x ->
                                                    fun x1 ->
                                                      fun x2 ->
                                                        fun x3 ->
                                                          Prims.strcat
                                                            (Prims.strcat
                                                               (Prims.strcat
                                                                  (Prims.strcat
                                                                    (Prims.strcat
                                                                    "stt_atomic "
                                                                    (Prims.strcat
                                                                    uu___11
                                                                    " #"))
                                                                    (Prims.strcat
                                                                    x " "))
                                                                  (Prims.strcat
                                                                    x1
                                                                    " (requires\n"))
                                                               (Prims.strcat
                                                                  x2
                                                                  ") (ensures\n"))
                                                            (Prims.strcat x3
                                                               ")"))) in
                                      FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Syntax.Printer.fst"
                                                 (Prims.of_int (238))
                                                 (Prims.of_int (6))
                                                 (Prims.of_int (243))
                                                 (Prims.of_int (37)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Syntax.Printer.fst"
                                                 (Prims.of_int (238))
                                                 (Prims.of_int (6))
                                                 (Prims.of_int (243))
                                                 (Prims.of_int (37)))))
                                        (Obj.magic uu___9)
                                        (fun uu___10 ->
                                           FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___11 ->
                                                uu___10
                                                  (observability_to_string
                                                     obs))) in
                                    Obj.magic
                                      (FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Syntax.Printer.fst"
                                                  (Prims.of_int (238))
                                                  (Prims.of_int (6))
                                                  (Prims.of_int (243))
                                                  (Prims.of_int (37)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Syntax.Printer.fst"
                                                  (Prims.of_int (238))
                                                  (Prims.of_int (6))
                                                  (Prims.of_int (243))
                                                  (Prims.of_int (37)))))
                                         (Obj.magic uu___8)
                                         (fun uu___9 ->
                                            FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___10 -> uu___9 uu___7))))
                                   uu___7) in
                          Obj.magic
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Syntax.Printer.fst"
                                        (Prims.of_int (238))
                                        (Prims.of_int (6))
                                        (Prims.of_int (243))
                                        (Prims.of_int (37)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Syntax.Printer.fst"
                                        (Prims.of_int (238))
                                        (Prims.of_int (6))
                                        (Prims.of_int (243))
                                        (Prims.of_int (37)))))
                               (Obj.magic uu___5)
                               (fun uu___6 ->
                                  FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___7 -> uu___6 uu___4)))) uu___4) in
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                              (Prims.of_int (238)) (Prims.of_int (6))
                              (Prims.of_int (243)) (Prims.of_int (37)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                              (Prims.of_int (238)) (Prims.of_int (6))
                              (Prims.of_int (243)) (Prims.of_int (37)))))
                     (Obj.magic uu___2)
                     (fun uu___3 ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___4 -> uu___3 uu___1)))) uu___1)
    | Pulse_Syntax_Base.C_STGhost (inames, s) ->
        let uu___ = term_to_string s.Pulse_Syntax_Base.post in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                   (Prims.of_int (250)) (Prims.of_int (14))
                   (Prims.of_int (250)) (Prims.of_int (37)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                   (Prims.of_int (246)) (Prims.of_int (6))
                   (Prims.of_int (250)) (Prims.of_int (37)))))
          (Obj.magic uu___)
          (fun uu___1 ->
             (fun uu___1 ->
                let uu___2 =
                  let uu___3 = term_to_string s.Pulse_Syntax_Base.pre in
                  FStar_Tactics_Effect.tac_bind
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                             (Prims.of_int (249)) (Prims.of_int (14))
                             (Prims.of_int (249)) (Prims.of_int (36)))))
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                             (Prims.of_int (246)) (Prims.of_int (6))
                             (Prims.of_int (250)) (Prims.of_int (37)))))
                    (Obj.magic uu___3)
                    (fun uu___4 ->
                       (fun uu___4 ->
                          let uu___5 =
                            let uu___6 = term_to_string inames in
                            FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Syntax.Printer.fst"
                                       (Prims.of_int (248))
                                       (Prims.of_int (14))
                                       (Prims.of_int (248))
                                       (Prims.of_int (37)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Syntax.Printer.fst"
                                       (Prims.of_int (246))
                                       (Prims.of_int (6))
                                       (Prims.of_int (250))
                                       (Prims.of_int (37)))))
                              (Obj.magic uu___6)
                              (fun uu___7 ->
                                 (fun uu___7 ->
                                    let uu___8 =
                                      let uu___9 =
                                        term_to_string
                                          s.Pulse_Syntax_Base.res in
                                      FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Syntax.Printer.fst"
                                                 (Prims.of_int (247))
                                                 (Prims.of_int (14))
                                                 (Prims.of_int (247))
                                                 (Prims.of_int (36)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "FStar.Printf.fst"
                                                 (Prims.of_int (122))
                                                 (Prims.of_int (8))
                                                 (Prims.of_int (124))
                                                 (Prims.of_int (44)))))
                                        (Obj.magic uu___9)
                                        (fun uu___10 ->
                                           FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___11 ->
                                                fun x ->
                                                  fun x1 ->
                                                    fun x2 ->
                                                      Prims.strcat
                                                        (Prims.strcat
                                                           (Prims.strcat
                                                              (Prims.strcat
                                                                 "stt_ghost "
                                                                 (Prims.strcat
                                                                    uu___10
                                                                    " "))
                                                              (Prims.strcat x
                                                                 " (requires\n"))
                                                           (Prims.strcat x1
                                                              ") (ensures\n"))
                                                        (Prims.strcat x2 ")"))) in
                                    Obj.magic
                                      (FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Syntax.Printer.fst"
                                                  (Prims.of_int (246))
                                                  (Prims.of_int (6))
                                                  (Prims.of_int (250))
                                                  (Prims.of_int (37)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Pulse.Syntax.Printer.fst"
                                                  (Prims.of_int (246))
                                                  (Prims.of_int (6))
                                                  (Prims.of_int (250))
                                                  (Prims.of_int (37)))))
                                         (Obj.magic uu___8)
                                         (fun uu___9 ->
                                            FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___10 -> uu___9 uu___7))))
                                   uu___7) in
                          Obj.magic
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Syntax.Printer.fst"
                                        (Prims.of_int (246))
                                        (Prims.of_int (6))
                                        (Prims.of_int (250))
                                        (Prims.of_int (37)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Syntax.Printer.fst"
                                        (Prims.of_int (246))
                                        (Prims.of_int (6))
                                        (Prims.of_int (250))
                                        (Prims.of_int (37)))))
                               (Obj.magic uu___5)
                               (fun uu___6 ->
                                  FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___7 -> uu___6 uu___4)))) uu___4) in
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                              (Prims.of_int (246)) (Prims.of_int (6))
                              (Prims.of_int (250)) (Prims.of_int (37)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                              (Prims.of_int (246)) (Prims.of_int (6))
                              (Prims.of_int (250)) (Prims.of_int (37)))))
                     (Obj.magic uu___2)
                     (fun uu___3 ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___4 -> uu___3 uu___1)))) uu___1)
let (term_opt_to_string :
  Pulse_Syntax_Base.term FStar_Pervasives_Native.option ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    (fun t ->
       match t with
       | FStar_Pervasives_Native.None ->
           Obj.magic
             (Obj.repr (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> "")))
       | FStar_Pervasives_Native.Some t1 ->
           Obj.magic (Obj.repr (term_to_string t1))) uu___
let (term_list_to_string :
  Prims.string ->
    Pulse_Syntax_Base.term Prims.list ->
      (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun sep ->
    fun t ->
      let uu___ = FStar_Tactics_Util.map term_to_string t in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                 (Prims.of_int (260)) (Prims.of_int (22))
                 (Prims.of_int (260)) (Prims.of_int (46)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                 (Prims.of_int (260)) (Prims.of_int (4)) (Prims.of_int (260))
                 (Prims.of_int (46))))) (Obj.magic uu___)
        (fun uu___1 ->
           FStar_Tactics_Effect.lift_div_tac
             (fun uu___2 -> FStar_String.concat sep uu___1))
let rec (st_term_to_string' :
  Prims.string ->
    Pulse_Syntax_Base.st_term ->
      (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun level ->
    fun t ->
      match t.Pulse_Syntax_Base.term1 with
      | Pulse_Syntax_Base.Tm_Return
          { Pulse_Syntax_Base.expected_type = uu___;
            Pulse_Syntax_Base.insert_eq = insert_eq;
            Pulse_Syntax_Base.term = term;_}
          ->
          let uu___1 = term_to_string term in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                     (Prims.of_int (268)) (Prims.of_int (8))
                     (Prims.of_int (268)) (Prims.of_int (29)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Prims.fst" (Prims.of_int (611))
                     (Prims.of_int (19)) (Prims.of_int (611))
                     (Prims.of_int (31))))) (Obj.magic uu___1)
            (fun uu___2 ->
               FStar_Tactics_Effect.lift_div_tac
                 (fun uu___3 ->
                    Prims.strcat
                      (Prims.strcat "return"
                         (Prims.strcat (if insert_eq then "" else "_noeq")
                            " ")) (Prims.strcat uu___2 "")))
      | Pulse_Syntax_Base.Tm_STApp
          { Pulse_Syntax_Base.head = head;
            Pulse_Syntax_Base.arg_qual = arg_qual;
            Pulse_Syntax_Base.arg = arg;_}
          ->
          let uu___ = term_to_string arg in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                     (Prims.of_int (275)) (Prims.of_int (8))
                     (Prims.of_int (275)) (Prims.of_int (28)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                     (Prims.of_int (271)) (Prims.of_int (6))
                     (Prims.of_int (275)) (Prims.of_int (28)))))
            (Obj.magic uu___)
            (fun uu___1 ->
               (fun uu___1 ->
                  let uu___2 =
                    let uu___3 =
                      let uu___4 = term_to_string head in
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "Pulse.Syntax.Printer.fst"
                                 (Prims.of_int (273)) (Prims.of_int (8))
                                 (Prims.of_int (273)) (Prims.of_int (29)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "FStar.Printf.fst"
                                 (Prims.of_int (122)) (Prims.of_int (8))
                                 (Prims.of_int (124)) (Prims.of_int (44)))))
                        (Obj.magic uu___4)
                        (fun uu___5 ->
                           FStar_Tactics_Effect.lift_div_tac
                             (fun uu___6 ->
                                fun x ->
                                  fun x1 ->
                                    Prims.strcat
                                      (Prims.strcat
                                         (Prims.strcat
                                            (Prims.strcat "("
                                               (Prims.strcat
                                                  (if dbg_printing
                                                   then "<stapp>"
                                                   else "") ""))
                                            (Prims.strcat uu___5 " "))
                                         (Prims.strcat x ""))
                                      (Prims.strcat x1 ")"))) in
                    FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                               (Prims.of_int (271)) (Prims.of_int (6))
                               (Prims.of_int (275)) (Prims.of_int (28)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                               (Prims.of_int (271)) (Prims.of_int (6))
                               (Prims.of_int (275)) (Prims.of_int (28)))))
                      (Obj.magic uu___3)
                      (fun uu___4 ->
                         FStar_Tactics_Effect.lift_div_tac
                           (fun uu___5 -> uu___4 (qual_to_string arg_qual))) in
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                                (Prims.of_int (271)) (Prims.of_int (6))
                                (Prims.of_int (275)) (Prims.of_int (28)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                                (Prims.of_int (271)) (Prims.of_int (6))
                                (Prims.of_int (275)) (Prims.of_int (28)))))
                       (Obj.magic uu___2)
                       (fun uu___3 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___4 -> uu___3 uu___1)))) uu___1)
      | Pulse_Syntax_Base.Tm_Bind
          { Pulse_Syntax_Base.binder = binder;
            Pulse_Syntax_Base.head1 = head; Pulse_Syntax_Base.body1 = body;_}
          ->
          let uu___ = st_term_to_string' level body in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                     (Prims.of_int (288)) (Prims.of_int (10))
                     (Prims.of_int (288)) (Prims.of_int (41)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                     (Prims.of_int (284)) (Prims.of_int (8))
                     (Prims.of_int (288)) (Prims.of_int (41)))))
            (Obj.magic uu___)
            (fun uu___1 ->
               (fun uu___1 ->
                  let uu___2 =
                    let uu___3 =
                      let uu___4 = st_term_to_string' level head in
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "Pulse.Syntax.Printer.fst"
                                 (Prims.of_int (286)) (Prims.of_int (10))
                                 (Prims.of_int (286)) (Prims.of_int (41)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "Pulse.Syntax.Printer.fst"
                                 (Prims.of_int (284)) (Prims.of_int (8))
                                 (Prims.of_int (288)) (Prims.of_int (41)))))
                        (Obj.magic uu___4)
                        (fun uu___5 ->
                           (fun uu___5 ->
                              let uu___6 =
                                let uu___7 = binder_to_string binder in
                                FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Syntax.Printer.fst"
                                           (Prims.of_int (285))
                                           (Prims.of_int (10))
                                           (Prims.of_int (285))
                                           (Prims.of_int (35)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "FStar.Printf.fst"
                                           (Prims.of_int (122))
                                           (Prims.of_int (8))
                                           (Prims.of_int (124))
                                           (Prims.of_int (44)))))
                                  (Obj.magic uu___7)
                                  (fun uu___8 ->
                                     FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___9 ->
                                          fun x ->
                                            fun x1 ->
                                              fun x2 ->
                                                Prims.strcat
                                                  (Prims.strcat
                                                     (Prims.strcat
                                                        (Prims.strcat "let "
                                                           (Prims.strcat
                                                              uu___8 " = "))
                                                        (Prims.strcat x ";\n"))
                                                     (Prims.strcat x1 ""))
                                                  (Prims.strcat x2 ""))) in
                              Obj.magic
                                (FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Syntax.Printer.fst"
                                            (Prims.of_int (284))
                                            (Prims.of_int (8))
                                            (Prims.of_int (288))
                                            (Prims.of_int (41)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Syntax.Printer.fst"
                                            (Prims.of_int (284))
                                            (Prims.of_int (8))
                                            (Prims.of_int (288))
                                            (Prims.of_int (41)))))
                                   (Obj.magic uu___6)
                                   (fun uu___7 ->
                                      FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___8 -> uu___7 uu___5))))
                             uu___5) in
                    FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                               (Prims.of_int (284)) (Prims.of_int (8))
                               (Prims.of_int (288)) (Prims.of_int (41)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                               (Prims.of_int (284)) (Prims.of_int (8))
                               (Prims.of_int (288)) (Prims.of_int (41)))))
                      (Obj.magic uu___3)
                      (fun uu___4 ->
                         FStar_Tactics_Effect.lift_div_tac
                           (fun uu___5 -> uu___4 level)) in
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                                (Prims.of_int (284)) (Prims.of_int (8))
                                (Prims.of_int (288)) (Prims.of_int (41)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                                (Prims.of_int (284)) (Prims.of_int (8))
                                (Prims.of_int (288)) (Prims.of_int (41)))))
                       (Obj.magic uu___2)
                       (fun uu___3 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___4 -> uu___3 uu___1)))) uu___1)
      | Pulse_Syntax_Base.Tm_TotBind
          { Pulse_Syntax_Base.binder1 = binder;
            Pulse_Syntax_Base.head2 = head; Pulse_Syntax_Base.body2 = body;_}
          ->
          let uu___ = st_term_to_string' level body in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                     (Prims.of_int (296)) (Prims.of_int (8))
                     (Prims.of_int (296)) (Prims.of_int (39)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                     (Prims.of_int (292)) (Prims.of_int (6))
                     (Prims.of_int (296)) (Prims.of_int (39)))))
            (Obj.magic uu___)
            (fun uu___1 ->
               (fun uu___1 ->
                  let uu___2 =
                    let uu___3 =
                      let uu___4 = term_to_string head in
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "Pulse.Syntax.Printer.fst"
                                 (Prims.of_int (294)) (Prims.of_int (8))
                                 (Prims.of_int (294)) (Prims.of_int (29)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "Pulse.Syntax.Printer.fst"
                                 (Prims.of_int (292)) (Prims.of_int (6))
                                 (Prims.of_int (296)) (Prims.of_int (39)))))
                        (Obj.magic uu___4)
                        (fun uu___5 ->
                           (fun uu___5 ->
                              let uu___6 =
                                let uu___7 = binder_to_string binder in
                                FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Syntax.Printer.fst"
                                           (Prims.of_int (293))
                                           (Prims.of_int (8))
                                           (Prims.of_int (293))
                                           (Prims.of_int (33)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "FStar.Printf.fst"
                                           (Prims.of_int (122))
                                           (Prims.of_int (8))
                                           (Prims.of_int (124))
                                           (Prims.of_int (44)))))
                                  (Obj.magic uu___7)
                                  (fun uu___8 ->
                                     FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___9 ->
                                          fun x ->
                                            fun x1 ->
                                              fun x2 ->
                                                Prims.strcat
                                                  (Prims.strcat
                                                     (Prims.strcat
                                                        (Prims.strcat
                                                           "let tot "
                                                           (Prims.strcat
                                                              uu___8 " = "))
                                                        (Prims.strcat x ";\n"))
                                                     (Prims.strcat x1 ""))
                                                  (Prims.strcat x2 ""))) in
                              Obj.magic
                                (FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Syntax.Printer.fst"
                                            (Prims.of_int (292))
                                            (Prims.of_int (6))
                                            (Prims.of_int (296))
                                            (Prims.of_int (39)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Syntax.Printer.fst"
                                            (Prims.of_int (292))
                                            (Prims.of_int (6))
                                            (Prims.of_int (296))
                                            (Prims.of_int (39)))))
                                   (Obj.magic uu___6)
                                   (fun uu___7 ->
                                      FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___8 -> uu___7 uu___5))))
                             uu___5) in
                    FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                               (Prims.of_int (292)) (Prims.of_int (6))
                               (Prims.of_int (296)) (Prims.of_int (39)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                               (Prims.of_int (292)) (Prims.of_int (6))
                               (Prims.of_int (296)) (Prims.of_int (39)))))
                      (Obj.magic uu___3)
                      (fun uu___4 ->
                         FStar_Tactics_Effect.lift_div_tac
                           (fun uu___5 -> uu___4 level)) in
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                                (Prims.of_int (292)) (Prims.of_int (6))
                                (Prims.of_int (296)) (Prims.of_int (39)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                                (Prims.of_int (292)) (Prims.of_int (6))
                                (Prims.of_int (296)) (Prims.of_int (39)))))
                       (Obj.magic uu___2)
                       (fun uu___3 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___4 -> uu___3 uu___1)))) uu___1)
      | Pulse_Syntax_Base.Tm_Abs
          { Pulse_Syntax_Base.b = b; Pulse_Syntax_Base.q = q;
            Pulse_Syntax_Base.ascription = c;
            Pulse_Syntax_Base.body = body;_}
          ->
          let uu___ =
            match c.Pulse_Syntax_Base.elaborated with
            | FStar_Pervasives_Native.None ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> "")))
            | FStar_Pervasives_Native.Some c1 ->
                Obj.magic
                  (Obj.repr
                     (let uu___1 = comp_to_string c1 in
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "Pulse.Syntax.Printer.fst"
                                 (Prims.of_int (305)) (Prims.of_int (73))
                                 (Prims.of_int (305)) (Prims.of_int (89)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "Prims.fst"
                                 (Prims.of_int (611)) (Prims.of_int (19))
                                 (Prims.of_int (611)) (Prims.of_int (31)))))
                        (Obj.magic uu___1)
                        (fun uu___2 ->
                           FStar_Tactics_Effect.lift_div_tac
                             (fun uu___3 -> Prims.strcat " <: " uu___2)))) in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                     (Prims.of_int (305)) (Prims.of_int (14))
                     (Prims.of_int (305)) (Prims.of_int (90)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                     (Prims.of_int (299)) (Prims.of_int (6))
                     (Prims.of_int (305)) (Prims.of_int (90)))))
            (Obj.magic uu___)
            (fun uu___1 ->
               (fun uu___1 ->
                  let uu___2 =
                    let uu___3 = st_term_to_string' (indent level) body in
                    FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                               (Prims.of_int (304)) (Prims.of_int (14))
                               (Prims.of_int (304)) (Prims.of_int (54)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                               (Prims.of_int (299)) (Prims.of_int (6))
                               (Prims.of_int (305)) (Prims.of_int (90)))))
                      (Obj.magic uu___3)
                      (fun uu___4 ->
                         (fun uu___4 ->
                            let uu___5 =
                              let uu___6 =
                                let uu___7 =
                                  match c.Pulse_Syntax_Base.annotated with
                                  | FStar_Pervasives_Native.None ->
                                      Obj.magic
                                        (Obj.repr
                                           (FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___8 -> "")))
                                  | FStar_Pervasives_Native.Some c1 ->
                                      Obj.magic
                                        (Obj.repr (comp_to_string c1)) in
                                FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Syntax.Printer.fst"
                                           (Prims.of_int (302))
                                           (Prims.of_int (14))
                                           (Prims.of_int (302))
                                           (Prims.of_int (80)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Syntax.Printer.fst"
                                           (Prims.of_int (299))
                                           (Prims.of_int (6))
                                           (Prims.of_int (305))
                                           (Prims.of_int (90)))))
                                  (Obj.magic uu___7)
                                  (fun uu___8 ->
                                     (fun uu___8 ->
                                        let uu___9 =
                                          let uu___10 = binder_to_string b in
                                          FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Syntax.Printer.fst"
                                                     (Prims.of_int (301))
                                                     (Prims.of_int (14))
                                                     (Prims.of_int (301))
                                                     (Prims.of_int (34)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "FStar.Printf.fst"
                                                     (Prims.of_int (122))
                                                     (Prims.of_int (8))
                                                     (Prims.of_int (124))
                                                     (Prims.of_int (44)))))
                                            (Obj.magic uu___10)
                                            (fun uu___11 ->
                                               FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___12 ->
                                                    fun x ->
                                                      fun x1 ->
                                                        fun x2 ->
                                                          fun x3 ->
                                                            Prims.strcat
                                                              (Prims.strcat
                                                                 (Prims.strcat
                                                                    (
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    "(fun ("
                                                                    (Prims.strcat
                                                                    (qual_to_string
                                                                    q) ""))
                                                                    (Prims.strcat
                                                                    uu___11
                                                                    ")\n"))
                                                                    (Prims.strcat
                                                                    x
                                                                    "\n ({\n"))
                                                                    (
                                                                    Prims.strcat
                                                                    x1 ""))
                                                                 (Prims.strcat
                                                                    x2 "\n}"))
                                                              (Prims.strcat
                                                                 x3 ")"))) in
                                        Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Syntax.Printer.fst"
                                                      (Prims.of_int (299))
                                                      (Prims.of_int (6))
                                                      (Prims.of_int (305))
                                                      (Prims.of_int (90)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Syntax.Printer.fst"
                                                      (Prims.of_int (299))
                                                      (Prims.of_int (6))
                                                      (Prims.of_int (305))
                                                      (Prims.of_int (90)))))
                                             (Obj.magic uu___9)
                                             (fun uu___10 ->
                                                FStar_Tactics_Effect.lift_div_tac
                                                  (fun uu___11 ->
                                                     uu___10 uu___8))))
                                       uu___8) in
                              FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Syntax.Printer.fst"
                                         (Prims.of_int (299))
                                         (Prims.of_int (6))
                                         (Prims.of_int (305))
                                         (Prims.of_int (90)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Syntax.Printer.fst"
                                         (Prims.of_int (299))
                                         (Prims.of_int (6))
                                         (Prims.of_int (305))
                                         (Prims.of_int (90)))))
                                (Obj.magic uu___6)
                                (fun uu___7 ->
                                   FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___8 -> uu___7 (indent level))) in
                            Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Syntax.Printer.fst"
                                          (Prims.of_int (299))
                                          (Prims.of_int (6))
                                          (Prims.of_int (305))
                                          (Prims.of_int (90)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Syntax.Printer.fst"
                                          (Prims.of_int (299))
                                          (Prims.of_int (6))
                                          (Prims.of_int (305))
                                          (Prims.of_int (90)))))
                                 (Obj.magic uu___5)
                                 (fun uu___6 ->
                                    FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___7 -> uu___6 uu___4)))) uu___4) in
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                                (Prims.of_int (299)) (Prims.of_int (6))
                                (Prims.of_int (305)) (Prims.of_int (90)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                                (Prims.of_int (299)) (Prims.of_int (6))
                                (Prims.of_int (305)) (Prims.of_int (90)))))
                       (Obj.magic uu___2)
                       (fun uu___3 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___4 -> uu___3 uu___1)))) uu___1)
      | Pulse_Syntax_Base.Tm_If
          { Pulse_Syntax_Base.b1 = b; Pulse_Syntax_Base.then_ = then_;
            Pulse_Syntax_Base.else_ = else_;
            Pulse_Syntax_Base.post1 = uu___;_}
          ->
          let uu___1 =
            let uu___2 = st_term_to_string' (indent level) else_ in
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                       (Prims.of_int (317)) (Prims.of_int (8))
                       (Prims.of_int (317)) (Prims.of_int (49)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                       (Prims.of_int (308)) (Prims.of_int (6))
                       (Prims.of_int (318)) (Prims.of_int (13)))))
              (Obj.magic uu___2)
              (fun uu___3 ->
                 (fun uu___3 ->
                    let uu___4 =
                      let uu___5 =
                        let uu___6 =
                          let uu___7 =
                            let uu___8 =
                              let uu___9 =
                                st_term_to_string' (indent level) then_ in
                              FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Syntax.Printer.fst"
                                         (Prims.of_int (312))
                                         (Prims.of_int (8))
                                         (Prims.of_int (312))
                                         (Prims.of_int (49)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Syntax.Printer.fst"
                                         (Prims.of_int (308))
                                         (Prims.of_int (6))
                                         (Prims.of_int (318))
                                         (Prims.of_int (13)))))
                                (Obj.magic uu___9)
                                (fun uu___10 ->
                                   (fun uu___10 ->
                                      let uu___11 =
                                        let uu___12 =
                                          let uu___13 =
                                            let uu___14 = term_to_string b in
                                            FStar_Tactics_Effect.tac_bind
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "Pulse.Syntax.Printer.fst"
                                                       (Prims.of_int (309))
                                                       (Prims.of_int (8))
                                                       (Prims.of_int (309))
                                                       (Prims.of_int (26)))))
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "FStar.Printf.fst"
                                                       (Prims.of_int (122))
                                                       (Prims.of_int (8))
                                                       (Prims.of_int (124))
                                                       (Prims.of_int (44)))))
                                              (Obj.magic uu___14)
                                              (fun uu___15 ->
                                                 FStar_Tactics_Effect.lift_div_tac
                                                   (fun uu___16 ->
                                                      fun x ->
                                                        fun x1 ->
                                                          fun x2 ->
                                                            fun x3 ->
                                                              fun x4 ->
                                                                fun x5 ->
                                                                  fun x6 ->
                                                                    fun x7 ->
                                                                    fun x8 ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    "if ("
                                                                    (Prims.strcat
                                                                    uu___15
                                                                    ")\n"))
                                                                    (Prims.strcat
                                                                    x "{\n"))
                                                                    (Prims.strcat
                                                                    x1 ""))
                                                                    (Prims.strcat
                                                                    x2 "\n"))
                                                                    (Prims.strcat
                                                                    x3 "}\n"))
                                                                    (Prims.strcat
                                                                    x4
                                                                    "else\n"))
                                                                    (Prims.strcat
                                                                    x5 "{\n"))
                                                                    (Prims.strcat
                                                                    x6 ""))
                                                                    (Prims.strcat
                                                                    x7 "\n"))
                                                                    (Prims.strcat
                                                                    x8 "}"))) in
                                          FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Syntax.Printer.fst"
                                                     (Prims.of_int (308))
                                                     (Prims.of_int (6))
                                                     (Prims.of_int (318))
                                                     (Prims.of_int (13)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Syntax.Printer.fst"
                                                     (Prims.of_int (308))
                                                     (Prims.of_int (6))
                                                     (Prims.of_int (318))
                                                     (Prims.of_int (13)))))
                                            (Obj.magic uu___13)
                                            (fun uu___14 ->
                                               FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___15 ->
                                                    uu___14 level)) in
                                        FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Syntax.Printer.fst"
                                                   (Prims.of_int (308))
                                                   (Prims.of_int (6))
                                                   (Prims.of_int (318))
                                                   (Prims.of_int (13)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Syntax.Printer.fst"
                                                   (Prims.of_int (308))
                                                   (Prims.of_int (6))
                                                   (Prims.of_int (318))
                                                   (Prims.of_int (13)))))
                                          (Obj.magic uu___12)
                                          (fun uu___13 ->
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___14 ->
                                                  uu___13 (indent level))) in
                                      Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Syntax.Printer.fst"
                                                    (Prims.of_int (308))
                                                    (Prims.of_int (6))
                                                    (Prims.of_int (318))
                                                    (Prims.of_int (13)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Syntax.Printer.fst"
                                                    (Prims.of_int (308))
                                                    (Prims.of_int (6))
                                                    (Prims.of_int (318))
                                                    (Prims.of_int (13)))))
                                           (Obj.magic uu___11)
                                           (fun uu___12 ->
                                              FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___13 ->
                                                   uu___12 uu___10))))
                                     uu___10) in
                            FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Syntax.Printer.fst"
                                       (Prims.of_int (308))
                                       (Prims.of_int (6))
                                       (Prims.of_int (318))
                                       (Prims.of_int (13)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Syntax.Printer.fst"
                                       (Prims.of_int (308))
                                       (Prims.of_int (6))
                                       (Prims.of_int (318))
                                       (Prims.of_int (13)))))
                              (Obj.magic uu___8)
                              (fun uu___9 ->
                                 FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___10 -> uu___9 level)) in
                          FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "Pulse.Syntax.Printer.fst"
                                     (Prims.of_int (308)) (Prims.of_int (6))
                                     (Prims.of_int (318)) (Prims.of_int (13)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "Pulse.Syntax.Printer.fst"
                                     (Prims.of_int (308)) (Prims.of_int (6))
                                     (Prims.of_int (318)) (Prims.of_int (13)))))
                            (Obj.magic uu___7)
                            (fun uu___8 ->
                               FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___9 -> uu___8 level)) in
                        FStar_Tactics_Effect.tac_bind
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "Pulse.Syntax.Printer.fst"
                                   (Prims.of_int (308)) (Prims.of_int (6))
                                   (Prims.of_int (318)) (Prims.of_int (13)))))
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "Pulse.Syntax.Printer.fst"
                                   (Prims.of_int (308)) (Prims.of_int (6))
                                   (Prims.of_int (318)) (Prims.of_int (13)))))
                          (Obj.magic uu___6)
                          (fun uu___7 ->
                             FStar_Tactics_Effect.lift_div_tac
                               (fun uu___8 -> uu___7 level)) in
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "Pulse.Syntax.Printer.fst"
                                 (Prims.of_int (308)) (Prims.of_int (6))
                                 (Prims.of_int (318)) (Prims.of_int (13)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "Pulse.Syntax.Printer.fst"
                                 (Prims.of_int (308)) (Prims.of_int (6))
                                 (Prims.of_int (318)) (Prims.of_int (13)))))
                        (Obj.magic uu___5)
                        (fun uu___6 ->
                           FStar_Tactics_Effect.lift_div_tac
                             (fun uu___7 -> uu___6 (indent level))) in
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "Pulse.Syntax.Printer.fst"
                                  (Prims.of_int (308)) (Prims.of_int (6))
                                  (Prims.of_int (318)) (Prims.of_int (13)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "Pulse.Syntax.Printer.fst"
                                  (Prims.of_int (308)) (Prims.of_int (6))
                                  (Prims.of_int (318)) (Prims.of_int (13)))))
                         (Obj.magic uu___4)
                         (fun uu___5 ->
                            FStar_Tactics_Effect.lift_div_tac
                              (fun uu___6 -> uu___5 uu___3)))) uu___3) in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                     (Prims.of_int (308)) (Prims.of_int (6))
                     (Prims.of_int (318)) (Prims.of_int (13)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                     (Prims.of_int (308)) (Prims.of_int (6))
                     (Prims.of_int (318)) (Prims.of_int (13)))))
            (Obj.magic uu___1)
            (fun uu___2 ->
               FStar_Tactics_Effect.lift_div_tac (fun uu___3 -> uu___2 level))
      | Pulse_Syntax_Base.Tm_Match
          { Pulse_Syntax_Base.sc = sc; Pulse_Syntax_Base.returns_ = uu___;
            Pulse_Syntax_Base.brs = brs;_}
          ->
          let uu___1 = branches_to_string brs in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                     (Prims.of_int (323)) (Prims.of_int (8))
                     (Prims.of_int (323)) (Prims.of_int (32)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                     (Prims.of_int (321)) (Prims.of_int (6))
                     (Prims.of_int (323)) (Prims.of_int (32)))))
            (Obj.magic uu___1)
            (fun uu___2 ->
               (fun uu___2 ->
                  let uu___3 =
                    let uu___4 = term_to_string sc in
                    FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                               (Prims.of_int (322)) (Prims.of_int (8))
                               (Prims.of_int (322)) (Prims.of_int (27)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "FStar.Printf.fst"
                               (Prims.of_int (122)) (Prims.of_int (8))
                               (Prims.of_int (124)) (Prims.of_int (44)))))
                      (Obj.magic uu___4)
                      (fun uu___5 ->
                         FStar_Tactics_Effect.lift_div_tac
                           (fun uu___6 ->
                              fun x ->
                                Prims.strcat
                                  (Prims.strcat "match ("
                                     (Prims.strcat uu___5 ") with "))
                                  (Prims.strcat x ""))) in
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                                (Prims.of_int (321)) (Prims.of_int (6))
                                (Prims.of_int (323)) (Prims.of_int (32)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                                (Prims.of_int (321)) (Prims.of_int (6))
                                (Prims.of_int (323)) (Prims.of_int (32)))))
                       (Obj.magic uu___3)
                       (fun uu___4 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___5 -> uu___4 uu___2)))) uu___2)
      | Pulse_Syntax_Base.Tm_IntroPure { Pulse_Syntax_Base.p3 = p;_} ->
          let uu___ = term_to_string' (indent level) p in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                     (Prims.of_int (328)) (Prims.of_int (8))
                     (Prims.of_int (328)) (Prims.of_int (42)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Prims.fst" (Prims.of_int (611))
                     (Prims.of_int (19)) (Prims.of_int (611))
                     (Prims.of_int (31))))) (Obj.magic uu___)
            (fun uu___1 ->
               FStar_Tactics_Effect.lift_div_tac
                 (fun uu___2 ->
                    Prims.strcat
                      (Prims.strcat "introduce pure (\n"
                         (Prims.strcat (indent level) ""))
                      (Prims.strcat uu___1 ")")))
      | Pulse_Syntax_Base.Tm_ElimExists { Pulse_Syntax_Base.p4 = p;_} ->
          let uu___ = term_to_string p in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                     (Prims.of_int (332)) (Prims.of_int (8))
                     (Prims.of_int (332)) (Prims.of_int (26)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Prims.fst" (Prims.of_int (611))
                     (Prims.of_int (19)) (Prims.of_int (611))
                     (Prims.of_int (31))))) (Obj.magic uu___)
            (fun uu___1 ->
               FStar_Tactics_Effect.lift_div_tac
                 (fun uu___2 ->
                    Prims.strcat "elim_exists " (Prims.strcat uu___1 "")))
      | Pulse_Syntax_Base.Tm_IntroExists
          { Pulse_Syntax_Base.p5 = p;
            Pulse_Syntax_Base.witnesses = witnesses;_}
          ->
          let uu___ = term_list_to_string " " witnesses in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                     (Prims.of_int (339)) (Prims.of_int (8))
                     (Prims.of_int (339)) (Prims.of_int (43)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                     (Prims.of_int (335)) (Prims.of_int (6))
                     (Prims.of_int (339)) (Prims.of_int (43)))))
            (Obj.magic uu___)
            (fun uu___1 ->
               (fun uu___1 ->
                  let uu___2 =
                    let uu___3 =
                      let uu___4 = term_to_string' (indent level) p in
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "Pulse.Syntax.Printer.fst"
                                 (Prims.of_int (337)) (Prims.of_int (8))
                                 (Prims.of_int (337)) (Prims.of_int (42)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "FStar.Printf.fst"
                                 (Prims.of_int (122)) (Prims.of_int (8))
                                 (Prims.of_int (124)) (Prims.of_int (44)))))
                        (Obj.magic uu___4)
                        (fun uu___5 ->
                           FStar_Tactics_Effect.lift_div_tac
                             (fun uu___6 ->
                                fun x ->
                                  fun x1 ->
                                    Prims.strcat
                                      (Prims.strcat
                                         (Prims.strcat
                                            (Prims.strcat "introduce\n"
                                               (Prims.strcat (indent level)
                                                  ""))
                                            (Prims.strcat uu___5 "\n"))
                                         (Prims.strcat x "with "))
                                      (Prims.strcat x1 ""))) in
                    FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                               (Prims.of_int (335)) (Prims.of_int (6))
                               (Prims.of_int (339)) (Prims.of_int (43)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                               (Prims.of_int (335)) (Prims.of_int (6))
                               (Prims.of_int (339)) (Prims.of_int (43)))))
                      (Obj.magic uu___3)
                      (fun uu___4 ->
                         FStar_Tactics_Effect.lift_div_tac
                           (fun uu___5 -> uu___4 level)) in
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                                (Prims.of_int (335)) (Prims.of_int (6))
                                (Prims.of_int (339)) (Prims.of_int (43)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                                (Prims.of_int (335)) (Prims.of_int (6))
                                (Prims.of_int (339)) (Prims.of_int (43)))))
                       (Obj.magic uu___2)
                       (fun uu___3 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___4 -> uu___3 uu___1)))) uu___1)
      | Pulse_Syntax_Base.Tm_While
          { Pulse_Syntax_Base.invariant = invariant;
            Pulse_Syntax_Base.condition = condition;
            Pulse_Syntax_Base.condition_var = uu___;
            Pulse_Syntax_Base.body3 = body;_}
          ->
          let uu___1 =
            let uu___2 = st_term_to_string' (indent level) body in
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                       (Prims.of_int (348)) (Prims.of_int (8))
                       (Prims.of_int (348)) (Prims.of_int (48)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                       (Prims.of_int (342)) (Prims.of_int (6))
                       (Prims.of_int (349)) (Prims.of_int (13)))))
              (Obj.magic uu___2)
              (fun uu___3 ->
                 (fun uu___3 ->
                    let uu___4 =
                      let uu___5 =
                        let uu___6 =
                          let uu___7 = term_to_string invariant in
                          FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "Pulse.Syntax.Printer.fst"
                                     (Prims.of_int (345)) (Prims.of_int (8))
                                     (Prims.of_int (345)) (Prims.of_int (34)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "Pulse.Syntax.Printer.fst"
                                     (Prims.of_int (342)) (Prims.of_int (6))
                                     (Prims.of_int (349)) (Prims.of_int (13)))))
                            (Obj.magic uu___7)
                            (fun uu___8 ->
                               (fun uu___8 ->
                                  let uu___9 =
                                    let uu___10 =
                                      let uu___11 =
                                        st_term_to_string' level condition in
                                      FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "Pulse.Syntax.Printer.fst"
                                                 (Prims.of_int (343))
                                                 (Prims.of_int (8))
                                                 (Prims.of_int (343))
                                                 (Prims.of_int (44)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "FStar.Printf.fst"
                                                 (Prims.of_int (122))
                                                 (Prims.of_int (8))
                                                 (Prims.of_int (124))
                                                 (Prims.of_int (44)))))
                                        (Obj.magic uu___11)
                                        (fun uu___12 ->
                                           FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___13 ->
                                                fun x ->
                                                  fun x1 ->
                                                    fun x2 ->
                                                      fun x3 ->
                                                        fun x4 ->
                                                          fun x5 ->
                                                            Prims.strcat
                                                              (Prims.strcat
                                                                 (Prims.strcat
                                                                    (
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    "while ("
                                                                    (Prims.strcat
                                                                    uu___12
                                                                    ")\n"))
                                                                    (Prims.strcat
                                                                    x
                                                                    "invariant "))
                                                                    (Prims.strcat
                                                                    x1 "\n"))
                                                                    (Prims.strcat
                                                                    x2 "{\n"))
                                                                    (
                                                                    Prims.strcat
                                                                    x3 ""))
                                                                 (Prims.strcat
                                                                    x4 "\n"))
                                                              (Prims.strcat
                                                                 x5 "}"))) in
                                    FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Syntax.Printer.fst"
                                               (Prims.of_int (342))
                                               (Prims.of_int (6))
                                               (Prims.of_int (349))
                                               (Prims.of_int (13)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "Pulse.Syntax.Printer.fst"
                                               (Prims.of_int (342))
                                               (Prims.of_int (6))
                                               (Prims.of_int (349))
                                               (Prims.of_int (13)))))
                                      (Obj.magic uu___10)
                                      (fun uu___11 ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___12 -> uu___11 level)) in
                                  Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Syntax.Printer.fst"
                                                (Prims.of_int (342))
                                                (Prims.of_int (6))
                                                (Prims.of_int (349))
                                                (Prims.of_int (13)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Pulse.Syntax.Printer.fst"
                                                (Prims.of_int (342))
                                                (Prims.of_int (6))
                                                (Prims.of_int (349))
                                                (Prims.of_int (13)))))
                                       (Obj.magic uu___9)
                                       (fun uu___10 ->
                                          FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___11 -> uu___10 uu___8))))
                                 uu___8) in
                        FStar_Tactics_Effect.tac_bind
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "Pulse.Syntax.Printer.fst"
                                   (Prims.of_int (342)) (Prims.of_int (6))
                                   (Prims.of_int (349)) (Prims.of_int (13)))))
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "Pulse.Syntax.Printer.fst"
                                   (Prims.of_int (342)) (Prims.of_int (6))
                                   (Prims.of_int (349)) (Prims.of_int (13)))))
                          (Obj.magic uu___6)
                          (fun uu___7 ->
                             FStar_Tactics_Effect.lift_div_tac
                               (fun uu___8 -> uu___7 level)) in
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "Pulse.Syntax.Printer.fst"
                                 (Prims.of_int (342)) (Prims.of_int (6))
                                 (Prims.of_int (349)) (Prims.of_int (13)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "Pulse.Syntax.Printer.fst"
                                 (Prims.of_int (342)) (Prims.of_int (6))
                                 (Prims.of_int (349)) (Prims.of_int (13)))))
                        (Obj.magic uu___5)
                        (fun uu___6 ->
                           FStar_Tactics_Effect.lift_div_tac
                             (fun uu___7 -> uu___6 (indent level))) in
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "Pulse.Syntax.Printer.fst"
                                  (Prims.of_int (342)) (Prims.of_int (6))
                                  (Prims.of_int (349)) (Prims.of_int (13)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "Pulse.Syntax.Printer.fst"
                                  (Prims.of_int (342)) (Prims.of_int (6))
                                  (Prims.of_int (349)) (Prims.of_int (13)))))
                         (Obj.magic uu___4)
                         (fun uu___5 ->
                            FStar_Tactics_Effect.lift_div_tac
                              (fun uu___6 -> uu___5 uu___3)))) uu___3) in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                     (Prims.of_int (342)) (Prims.of_int (6))
                     (Prims.of_int (349)) (Prims.of_int (13)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                     (Prims.of_int (342)) (Prims.of_int (6))
                     (Prims.of_int (349)) (Prims.of_int (13)))))
            (Obj.magic uu___1)
            (fun uu___2 ->
               FStar_Tactics_Effect.lift_div_tac (fun uu___3 -> uu___2 level))
      | Pulse_Syntax_Base.Tm_Par
          { Pulse_Syntax_Base.pre1 = pre1; Pulse_Syntax_Base.body11 = body1;
            Pulse_Syntax_Base.post11 = post1; Pulse_Syntax_Base.pre2 = pre2;
            Pulse_Syntax_Base.body21 = body2;
            Pulse_Syntax_Base.post2 = post2;_}
          ->
          let uu___ = term_to_string post2 in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                     (Prims.of_int (358)) (Prims.of_int (8))
                     (Prims.of_int (358)) (Prims.of_int (30)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                     (Prims.of_int (352)) (Prims.of_int (6))
                     (Prims.of_int (358)) (Prims.of_int (30)))))
            (Obj.magic uu___)
            (fun uu___1 ->
               (fun uu___1 ->
                  let uu___2 =
                    let uu___3 = st_term_to_string' level body2 in
                    FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                               (Prims.of_int (357)) (Prims.of_int (8))
                               (Prims.of_int (357)) (Prims.of_int (40)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                               (Prims.of_int (352)) (Prims.of_int (6))
                               (Prims.of_int (358)) (Prims.of_int (30)))))
                      (Obj.magic uu___3)
                      (fun uu___4 ->
                         (fun uu___4 ->
                            let uu___5 =
                              let uu___6 = term_to_string pre2 in
                              FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Syntax.Printer.fst"
                                         (Prims.of_int (356))
                                         (Prims.of_int (8))
                                         (Prims.of_int (356))
                                         (Prims.of_int (29)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Syntax.Printer.fst"
                                         (Prims.of_int (352))
                                         (Prims.of_int (6))
                                         (Prims.of_int (358))
                                         (Prims.of_int (30)))))
                                (Obj.magic uu___6)
                                (fun uu___7 ->
                                   (fun uu___7 ->
                                      let uu___8 =
                                        let uu___9 = term_to_string post1 in
                                        FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Syntax.Printer.fst"
                                                   (Prims.of_int (355))
                                                   (Prims.of_int (8))
                                                   (Prims.of_int (355))
                                                   (Prims.of_int (30)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Pulse.Syntax.Printer.fst"
                                                   (Prims.of_int (352))
                                                   (Prims.of_int (6))
                                                   (Prims.of_int (358))
                                                   (Prims.of_int (30)))))
                                          (Obj.magic uu___9)
                                          (fun uu___10 ->
                                             (fun uu___10 ->
                                                let uu___11 =
                                                  let uu___12 =
                                                    st_term_to_string' level
                                                      body1 in
                                                  FStar_Tactics_Effect.tac_bind
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Syntax.Printer.fst"
                                                             (Prims.of_int (354))
                                                             (Prims.of_int (8))
                                                             (Prims.of_int (354))
                                                             (Prims.of_int (40)))))
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Pulse.Syntax.Printer.fst"
                                                             (Prims.of_int (352))
                                                             (Prims.of_int (6))
                                                             (Prims.of_int (358))
                                                             (Prims.of_int (30)))))
                                                    (Obj.magic uu___12)
                                                    (fun uu___13 ->
                                                       (fun uu___13 ->
                                                          let uu___14 =
                                                            let uu___15 =
                                                              term_to_string
                                                                pre1 in
                                                            FStar_Tactics_Effect.tac_bind
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (353))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (353))
                                                                    (Prims.of_int (29)))))
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (122))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (44)))))
                                                              (Obj.magic
                                                                 uu___15)
                                                              (fun uu___16 ->
                                                                 FStar_Tactics_Effect.lift_div_tac
                                                                   (fun
                                                                    uu___17
                                                                    ->
                                                                    fun x ->
                                                                    fun x1 ->
                                                                    fun x2 ->
                                                                    fun x3 ->
                                                                    fun x4 ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    "par (<"
                                                                    (Prims.strcat
                                                                    uu___16
                                                                    "> ("))
                                                                    (Prims.strcat
                                                                    x ") <"))
                                                                    (Prims.strcat
                                                                    x1 ") (<"))
                                                                    (Prims.strcat
                                                                    x2 "> ("))
                                                                    (Prims.strcat
                                                                    x3 ") <"))
                                                                    (Prims.strcat
                                                                    x4 ")"))) in
                                                          Obj.magic
                                                            (FStar_Tactics_Effect.tac_bind
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (352))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (358))
                                                                    (Prims.of_int (30)))))
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (352))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (358))
                                                                    (Prims.of_int (30)))))
                                                               (Obj.magic
                                                                  uu___14)
                                                               (fun uu___15
                                                                  ->
                                                                  FStar_Tactics_Effect.lift_div_tac
                                                                    (
                                                                    fun
                                                                    uu___16
                                                                    ->
                                                                    uu___15
                                                                    uu___13))))
                                                         uu___13) in
                                                Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Syntax.Printer.fst"
                                                              (Prims.of_int (352))
                                                              (Prims.of_int (6))
                                                              (Prims.of_int (358))
                                                              (Prims.of_int (30)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "Pulse.Syntax.Printer.fst"
                                                              (Prims.of_int (352))
                                                              (Prims.of_int (6))
                                                              (Prims.of_int (358))
                                                              (Prims.of_int (30)))))
                                                     (Obj.magic uu___11)
                                                     (fun uu___12 ->
                                                        FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___13 ->
                                                             uu___12 uu___10))))
                                               uu___10) in
                                      Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Syntax.Printer.fst"
                                                    (Prims.of_int (352))
                                                    (Prims.of_int (6))
                                                    (Prims.of_int (358))
                                                    (Prims.of_int (30)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Syntax.Printer.fst"
                                                    (Prims.of_int (352))
                                                    (Prims.of_int (6))
                                                    (Prims.of_int (358))
                                                    (Prims.of_int (30)))))
                                           (Obj.magic uu___8)
                                           (fun uu___9 ->
                                              FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___10 -> uu___9 uu___7))))
                                     uu___7) in
                            Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Syntax.Printer.fst"
                                          (Prims.of_int (352))
                                          (Prims.of_int (6))
                                          (Prims.of_int (358))
                                          (Prims.of_int (30)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Syntax.Printer.fst"
                                          (Prims.of_int (352))
                                          (Prims.of_int (6))
                                          (Prims.of_int (358))
                                          (Prims.of_int (30)))))
                                 (Obj.magic uu___5)
                                 (fun uu___6 ->
                                    FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___7 -> uu___6 uu___4)))) uu___4) in
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                                (Prims.of_int (352)) (Prims.of_int (6))
                                (Prims.of_int (358)) (Prims.of_int (30)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                                (Prims.of_int (352)) (Prims.of_int (6))
                                (Prims.of_int (358)) (Prims.of_int (30)))))
                       (Obj.magic uu___2)
                       (fun uu___3 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___4 -> uu___3 uu___1)))) uu___1)
      | Pulse_Syntax_Base.Tm_Rewrite
          { Pulse_Syntax_Base.t11 = t1; Pulse_Syntax_Base.t21 = t2;
            Pulse_Syntax_Base.tac_opt2 = uu___;_}
          ->
          let uu___1 = term_to_string t2 in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                     (Prims.of_int (363)) (Prims.of_int (8))
                     (Prims.of_int (363)) (Prims.of_int (27)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                     (Prims.of_int (361)) (Prims.of_int (7))
                     (Prims.of_int (363)) (Prims.of_int (27)))))
            (Obj.magic uu___1)
            (fun uu___2 ->
               (fun uu___2 ->
                  let uu___3 =
                    let uu___4 = term_to_string t1 in
                    FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                               (Prims.of_int (362)) (Prims.of_int (8))
                               (Prims.of_int (362)) (Prims.of_int (27)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "FStar.Printf.fst"
                               (Prims.of_int (122)) (Prims.of_int (8))
                               (Prims.of_int (124)) (Prims.of_int (44)))))
                      (Obj.magic uu___4)
                      (fun uu___5 ->
                         FStar_Tactics_Effect.lift_div_tac
                           (fun uu___6 ->
                              fun x ->
                                Prims.strcat
                                  (Prims.strcat "rewrite "
                                     (Prims.strcat uu___5 " as "))
                                  (Prims.strcat x ""))) in
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                                (Prims.of_int (361)) (Prims.of_int (7))
                                (Prims.of_int (363)) (Prims.of_int (27)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                                (Prims.of_int (361)) (Prims.of_int (7))
                                (Prims.of_int (363)) (Prims.of_int (27)))))
                       (Obj.magic uu___3)
                       (fun uu___4 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___5 -> uu___4 uu___2)))) uu___2)
      | Pulse_Syntax_Base.Tm_WithLocal
          { Pulse_Syntax_Base.binder2 = binder;
            Pulse_Syntax_Base.initializer1 = initializer1;
            Pulse_Syntax_Base.body4 = body;_}
          ->
          let uu___ = st_term_to_string' level body in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                     (Prims.of_int (370)) (Prims.of_int (8))
                     (Prims.of_int (370)) (Prims.of_int (39)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                     (Prims.of_int (366)) (Prims.of_int (6))
                     (Prims.of_int (370)) (Prims.of_int (39)))))
            (Obj.magic uu___)
            (fun uu___1 ->
               (fun uu___1 ->
                  let uu___2 =
                    let uu___3 =
                      let uu___4 = term_to_string initializer1 in
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "Pulse.Syntax.Printer.fst"
                                 (Prims.of_int (368)) (Prims.of_int (8))
                                 (Prims.of_int (368)) (Prims.of_int (36)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "Pulse.Syntax.Printer.fst"
                                 (Prims.of_int (366)) (Prims.of_int (6))
                                 (Prims.of_int (370)) (Prims.of_int (39)))))
                        (Obj.magic uu___4)
                        (fun uu___5 ->
                           (fun uu___5 ->
                              let uu___6 =
                                let uu___7 = binder_to_string binder in
                                FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Syntax.Printer.fst"
                                           (Prims.of_int (367))
                                           (Prims.of_int (8))
                                           (Prims.of_int (367))
                                           (Prims.of_int (33)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "FStar.Printf.fst"
                                           (Prims.of_int (122))
                                           (Prims.of_int (8))
                                           (Prims.of_int (124))
                                           (Prims.of_int (44)))))
                                  (Obj.magic uu___7)
                                  (fun uu___8 ->
                                     FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___9 ->
                                          fun x ->
                                            fun x1 ->
                                              fun x2 ->
                                                Prims.strcat
                                                  (Prims.strcat
                                                     (Prims.strcat
                                                        (Prims.strcat
                                                           "let mut "
                                                           (Prims.strcat
                                                              uu___8 " = "))
                                                        (Prims.strcat x ";\n"))
                                                     (Prims.strcat x1 ""))
                                                  (Prims.strcat x2 ""))) in
                              Obj.magic
                                (FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Syntax.Printer.fst"
                                            (Prims.of_int (366))
                                            (Prims.of_int (6))
                                            (Prims.of_int (370))
                                            (Prims.of_int (39)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Syntax.Printer.fst"
                                            (Prims.of_int (366))
                                            (Prims.of_int (6))
                                            (Prims.of_int (370))
                                            (Prims.of_int (39)))))
                                   (Obj.magic uu___6)
                                   (fun uu___7 ->
                                      FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___8 -> uu___7 uu___5))))
                             uu___5) in
                    FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                               (Prims.of_int (366)) (Prims.of_int (6))
                               (Prims.of_int (370)) (Prims.of_int (39)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                               (Prims.of_int (366)) (Prims.of_int (6))
                               (Prims.of_int (370)) (Prims.of_int (39)))))
                      (Obj.magic uu___3)
                      (fun uu___4 ->
                         FStar_Tactics_Effect.lift_div_tac
                           (fun uu___5 -> uu___4 level)) in
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                                (Prims.of_int (366)) (Prims.of_int (6))
                                (Prims.of_int (370)) (Prims.of_int (39)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                                (Prims.of_int (366)) (Prims.of_int (6))
                                (Prims.of_int (370)) (Prims.of_int (39)))))
                       (Obj.magic uu___2)
                       (fun uu___3 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___4 -> uu___3 uu___1)))) uu___1)
      | Pulse_Syntax_Base.Tm_WithLocalArray
          { Pulse_Syntax_Base.binder3 = binder;
            Pulse_Syntax_Base.initializer2 = initializer1;
            Pulse_Syntax_Base.length = length;
            Pulse_Syntax_Base.body5 = body;_}
          ->
          let uu___ = st_term_to_string' level body in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                     (Prims.of_int (378)) (Prims.of_int (8))
                     (Prims.of_int (378)) (Prims.of_int (39)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                     (Prims.of_int (373)) (Prims.of_int (6))
                     (Prims.of_int (378)) (Prims.of_int (39)))))
            (Obj.magic uu___)
            (fun uu___1 ->
               (fun uu___1 ->
                  let uu___2 =
                    let uu___3 =
                      let uu___4 = term_to_string length in
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "Pulse.Syntax.Printer.fst"
                                 (Prims.of_int (376)) (Prims.of_int (8))
                                 (Prims.of_int (376)) (Prims.of_int (31)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "Pulse.Syntax.Printer.fst"
                                 (Prims.of_int (373)) (Prims.of_int (6))
                                 (Prims.of_int (378)) (Prims.of_int (39)))))
                        (Obj.magic uu___4)
                        (fun uu___5 ->
                           (fun uu___5 ->
                              let uu___6 =
                                let uu___7 = term_to_string initializer1 in
                                FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Syntax.Printer.fst"
                                           (Prims.of_int (375))
                                           (Prims.of_int (8))
                                           (Prims.of_int (375))
                                           (Prims.of_int (36)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Syntax.Printer.fst"
                                           (Prims.of_int (373))
                                           (Prims.of_int (6))
                                           (Prims.of_int (378))
                                           (Prims.of_int (39)))))
                                  (Obj.magic uu___7)
                                  (fun uu___8 ->
                                     (fun uu___8 ->
                                        let uu___9 =
                                          let uu___10 =
                                            binder_to_string binder in
                                          FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Syntax.Printer.fst"
                                                     (Prims.of_int (374))
                                                     (Prims.of_int (8))
                                                     (Prims.of_int (374))
                                                     (Prims.of_int (33)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "FStar.Printf.fst"
                                                     (Prims.of_int (122))
                                                     (Prims.of_int (8))
                                                     (Prims.of_int (124))
                                                     (Prims.of_int (44)))))
                                            (Obj.magic uu___10)
                                            (fun uu___11 ->
                                               FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___12 ->
                                                    fun x ->
                                                      fun x1 ->
                                                        fun x2 ->
                                                          fun x3 ->
                                                            Prims.strcat
                                                              (Prims.strcat
                                                                 (Prims.strcat
                                                                    (
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    "let mut "
                                                                    (Prims.strcat
                                                                    uu___11
                                                                    " = [| "))
                                                                    (Prims.strcat
                                                                    x "; "))
                                                                    (
                                                                    Prims.strcat
                                                                    x1
                                                                    " |]\n"))
                                                                 (Prims.strcat
                                                                    x2 ""))
                                                              (Prims.strcat
                                                                 x3 ""))) in
                                        Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Syntax.Printer.fst"
                                                      (Prims.of_int (373))
                                                      (Prims.of_int (6))
                                                      (Prims.of_int (378))
                                                      (Prims.of_int (39)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Syntax.Printer.fst"
                                                      (Prims.of_int (373))
                                                      (Prims.of_int (6))
                                                      (Prims.of_int (378))
                                                      (Prims.of_int (39)))))
                                             (Obj.magic uu___9)
                                             (fun uu___10 ->
                                                FStar_Tactics_Effect.lift_div_tac
                                                  (fun uu___11 ->
                                                     uu___10 uu___8))))
                                       uu___8) in
                              Obj.magic
                                (FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Syntax.Printer.fst"
                                            (Prims.of_int (373))
                                            (Prims.of_int (6))
                                            (Prims.of_int (378))
                                            (Prims.of_int (39)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Syntax.Printer.fst"
                                            (Prims.of_int (373))
                                            (Prims.of_int (6))
                                            (Prims.of_int (378))
                                            (Prims.of_int (39)))))
                                   (Obj.magic uu___6)
                                   (fun uu___7 ->
                                      FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___8 -> uu___7 uu___5))))
                             uu___5) in
                    FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                               (Prims.of_int (373)) (Prims.of_int (6))
                               (Prims.of_int (378)) (Prims.of_int (39)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                               (Prims.of_int (373)) (Prims.of_int (6))
                               (Prims.of_int (378)) (Prims.of_int (39)))))
                      (Obj.magic uu___3)
                      (fun uu___4 ->
                         FStar_Tactics_Effect.lift_div_tac
                           (fun uu___5 -> uu___4 level)) in
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                                (Prims.of_int (373)) (Prims.of_int (6))
                                (Prims.of_int (378)) (Prims.of_int (39)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                                (Prims.of_int (373)) (Prims.of_int (6))
                                (Prims.of_int (378)) (Prims.of_int (39)))))
                       (Obj.magic uu___2)
                       (fun uu___3 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___4 -> uu___3 uu___1)))) uu___1)
      | Pulse_Syntax_Base.Tm_Admit
          { Pulse_Syntax_Base.ctag = ctag; Pulse_Syntax_Base.u1 = u;
            Pulse_Syntax_Base.typ = typ; Pulse_Syntax_Base.post3 = post;_}
          ->
          let uu___ =
            match post with
            | FStar_Pervasives_Native.None ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> "")))
            | FStar_Pervasives_Native.Some post1 ->
                Obj.magic
                  (Obj.repr
                     (let uu___1 = term_to_string post1 in
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "Pulse.Syntax.Printer.fst"
                                 (Prims.of_int (390)) (Prims.of_int (38))
                                 (Prims.of_int (390)) (Prims.of_int (59)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "Prims.fst"
                                 (Prims.of_int (611)) (Prims.of_int (19))
                                 (Prims.of_int (611)) (Prims.of_int (31)))))
                        (Obj.magic uu___1)
                        (fun uu___2 ->
                           FStar_Tactics_Effect.lift_div_tac
                             (fun uu___3 ->
                                Prims.strcat " " (Prims.strcat uu___2 ""))))) in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                     (Prims.of_int (388)) (Prims.of_int (8))
                     (Prims.of_int (390)) (Prims.of_int (60)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                     (Prims.of_int (381)) (Prims.of_int (6))
                     (Prims.of_int (390)) (Prims.of_int (60)))))
            (Obj.magic uu___)
            (fun uu___1 ->
               (fun uu___1 ->
                  let uu___2 =
                    let uu___3 = term_to_string typ in
                    FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                               (Prims.of_int (387)) (Prims.of_int (8))
                               (Prims.of_int (387)) (Prims.of_int (28)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "FStar.Printf.fst"
                               (Prims.of_int (122)) (Prims.of_int (8))
                               (Prims.of_int (124)) (Prims.of_int (44)))))
                      (Obj.magic uu___3)
                      (fun uu___4 ->
                         FStar_Tactics_Effect.lift_div_tac
                           (fun uu___5 ->
                              fun x ->
                                Prims.strcat
                                  (Prims.strcat
                                     (Prims.strcat
                                        (Prims.strcat ""
                                           (Prims.strcat
                                              (match ctag with
                                               | Pulse_Syntax_Base.STT ->
                                                   "stt_admit"
                                               | Pulse_Syntax_Base.STT_Atomic
                                                   -> "stt_atomic_admit"
                                               | Pulse_Syntax_Base.STT_Ghost
                                                   -> "stt_ghost_admit") "<"))
                                        (Prims.strcat
                                           (universe_to_string Prims.int_zero
                                              u) "> "))
                                     (Prims.strcat uu___4 ""))
                                  (Prims.strcat x ""))) in
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                                (Prims.of_int (381)) (Prims.of_int (6))
                                (Prims.of_int (390)) (Prims.of_int (60)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                                (Prims.of_int (381)) (Prims.of_int (6))
                                (Prims.of_int (390)) (Prims.of_int (60)))))
                       (Obj.magic uu___2)
                       (fun uu___3 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___4 -> uu___3 uu___1)))) uu___1)
      | Pulse_Syntax_Base.Tm_Unreachable { Pulse_Syntax_Base.c = c;_} ->
          let uu___ = comp_to_string c in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                     (Prims.of_int (392)) (Prims.of_int (57))
                     (Prims.of_int (392)) (Prims.of_int (75)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Prims.fst" (Prims.of_int (611))
                     (Prims.of_int (19)) (Prims.of_int (611))
                     (Prims.of_int (31))))) (Obj.magic uu___)
            (fun uu___1 ->
               FStar_Tactics_Effect.lift_div_tac
                 (fun uu___2 ->
                    Prims.strcat "unreachable #" (Prims.strcat uu___1 " ()")))
      | Pulse_Syntax_Base.Tm_ProofHintWithBinders
          { Pulse_Syntax_Base.hint_type = hint_type;
            Pulse_Syntax_Base.binders = binders; Pulse_Syntax_Base.t = t1;_}
          ->
          let uu___ =
            match binders with
            | [] ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> "")))
            | uu___1 ->
                Obj.magic
                  (Obj.repr
                     (let uu___2 =
                        let uu___3 =
                          FStar_Tactics_Util.map binder_to_string binders in
                        FStar_Tactics_Effect.tac_bind
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "Pulse.Syntax.Printer.fst"
                                   (Prims.of_int (398)) (Prims.of_int (53))
                                   (Prims.of_int (398)) (Prims.of_int (85)))))
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "Pulse.Syntax.Printer.fst"
                                   (Prims.of_int (398)) (Prims.of_int (34))
                                   (Prims.of_int (398)) (Prims.of_int (86)))))
                          (Obj.magic uu___3)
                          (fun uu___4 ->
                             FStar_Tactics_Effect.lift_div_tac
                               (fun uu___5 -> FStar_String.concat " " uu___4)) in
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "Pulse.Syntax.Printer.fst"
                                 (Prims.of_int (398)) (Prims.of_int (34))
                                 (Prims.of_int (398)) (Prims.of_int (86)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range "Prims.fst"
                                 (Prims.of_int (611)) (Prims.of_int (19))
                                 (Prims.of_int (611)) (Prims.of_int (31)))))
                        (Obj.magic uu___2)
                        (fun uu___3 ->
                           FStar_Tactics_Effect.lift_div_tac
                             (fun uu___4 ->
                                Prims.strcat "with "
                                  (Prims.strcat uu___3 "."))))) in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                     (Prims.of_int (396)) (Prims.of_int (8))
                     (Prims.of_int (398)) (Prims.of_int (86)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                     (Prims.of_int (399)) (Prims.of_int (8))
                     (Prims.of_int (424)) (Prims.of_int (36)))))
            (Obj.magic uu___)
            (fun uu___1 ->
               (fun with_prefix ->
                  let uu___1 =
                    Obj.magic
                      (FStar_Tactics_Effect.lift_div_tac
                         (fun uu___2 ->
                            fun uu___3 ->
                              match uu___3 with
                              | FStar_Pervasives_Native.None -> ""
                              | FStar_Pervasives_Native.Some l ->
                                  Prims.strcat " ["
                                    (Prims.strcat
                                       (FStar_String.concat "; " l) "]"))) in
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                                (Prims.of_int (400)) (Prims.of_int (28))
                                (Prims.of_int (402)) (Prims.of_int (58)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                                (Prims.of_int (403)) (Prims.of_int (8))
                                (Prims.of_int (424)) (Prims.of_int (36)))))
                       (Obj.magic uu___1)
                       (fun uu___2 ->
                          (fun names_to_string ->
                             let uu___2 =
                               match hint_type with
                               | Pulse_Syntax_Base.ASSERT
                                   { Pulse_Syntax_Base.p = p;_} ->
                                   Obj.magic
                                     (Obj.repr
                                        (let uu___3 = term_to_string p in
                                         FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Syntax.Printer.fst"
                                                    (Prims.of_int (406))
                                                    (Prims.of_int (36))
                                                    (Prims.of_int (406))
                                                    (Prims.of_int (52)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Syntax.Printer.fst"
                                                    (Prims.of_int (406))
                                                    (Prims.of_int (26))
                                                    (Prims.of_int (406))
                                                    (Prims.of_int (52)))))
                                           (Obj.magic uu___3)
                                           (fun uu___4 ->
                                              FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___5 ->
                                                   ("assert", uu___4)))))
                               | Pulse_Syntax_Base.UNFOLD
                                   { Pulse_Syntax_Base.names1 = names;
                                     Pulse_Syntax_Base.p2 = p;_}
                                   ->
                                   Obj.magic
                                     (Obj.repr
                                        (let uu___3 = term_to_string p in
                                         FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Syntax.Printer.fst"
                                                    (Prims.of_int (407))
                                                    (Prims.of_int (77))
                                                    (Prims.of_int (407))
                                                    (Prims.of_int (93)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Syntax.Printer.fst"
                                                    (Prims.of_int (407))
                                                    (Prims.of_int (33))
                                                    (Prims.of_int (407))
                                                    (Prims.of_int (93)))))
                                           (Obj.magic uu___3)
                                           (fun uu___4 ->
                                              FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___5 ->
                                                   ((Prims.strcat "unfold"
                                                       (Prims.strcat
                                                          (names_to_string
                                                             names) "")),
                                                     uu___4)))))
                               | Pulse_Syntax_Base.FOLD
                                   { Pulse_Syntax_Base.names = names;
                                     Pulse_Syntax_Base.p1 = p;_}
                                   ->
                                   Obj.magic
                                     (Obj.repr
                                        (let uu___3 = term_to_string p in
                                         FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Syntax.Printer.fst"
                                                    (Prims.of_int (408))
                                                    (Prims.of_int (73))
                                                    (Prims.of_int (408))
                                                    (Prims.of_int (89)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Syntax.Printer.fst"
                                                    (Prims.of_int (408))
                                                    (Prims.of_int (31))
                                                    (Prims.of_int (408))
                                                    (Prims.of_int (89)))))
                                           (Obj.magic uu___3)
                                           (fun uu___4 ->
                                              FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___5 ->
                                                   ((Prims.strcat "fold"
                                                       (Prims.strcat
                                                          (names_to_string
                                                             names) "")),
                                                     uu___4)))))
                               | Pulse_Syntax_Base.RENAME
                                   { Pulse_Syntax_Base.pairs = pairs;
                                     Pulse_Syntax_Base.goal = goal;
                                     Pulse_Syntax_Base.tac_opt = uu___3;_}
                                   ->
                                   Obj.magic
                                     (Obj.repr
                                        (let uu___4 =
                                           let uu___5 =
                                             let uu___6 =
                                               FStar_Tactics_Util.map
                                                 (fun uu___7 ->
                                                    match uu___7 with
                                                    | (x, y) ->
                                                        let uu___8 =
                                                          term_to_string y in
                                                        FStar_Tactics_Effect.tac_bind
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Syntax.Printer.fst"
                                                                   (Prims.of_int (413))
                                                                   (Prims.of_int (69))
                                                                   (Prims.of_int (413))
                                                                   (Prims.of_int (87)))))
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "Pulse.Syntax.Printer.fst"
                                                                   (Prims.of_int (413))
                                                                   (Prims.of_int (31))
                                                                   (Prims.of_int (413))
                                                                   (Prims.of_int (87)))))
                                                          (Obj.magic uu___8)
                                                          (fun uu___9 ->
                                                             (fun uu___9 ->
                                                                let uu___10 =
                                                                  let uu___11
                                                                    =
                                                                    term_to_string
                                                                    x in
                                                                  FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (413))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (413))
                                                                    (Prims.of_int (68)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (122))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (124))
                                                                    (Prims.of_int (44)))))
                                                                    (
                                                                    Obj.magic
                                                                    uu___11)
                                                                    (
                                                                    fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    fun x1 ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    ""
                                                                    (Prims.strcat
                                                                    uu___12
                                                                    " as "))
                                                                    (Prims.strcat
                                                                    x1 ""))) in
                                                                Obj.magic
                                                                  (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (413))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (413))
                                                                    (Prims.of_int (87)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (413))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (413))
                                                                    (Prims.of_int (87)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    uu___11
                                                                    uu___9))))
                                                               uu___9)) pairs in
                                             FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Syntax.Printer.fst"
                                                        (Prims.of_int (412))
                                                        (Prims.of_int (14))
                                                        (Prims.of_int (414))
                                                        (Prims.of_int (20)))))
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Pulse.Syntax.Printer.fst"
                                                        (Prims.of_int (411))
                                                        (Prims.of_int (12))
                                                        (Prims.of_int (414))
                                                        (Prims.of_int (21)))))
                                               (Obj.magic uu___6)
                                               (fun uu___7 ->
                                                  FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___8 ->
                                                       FStar_String.concat
                                                         ", " uu___7)) in
                                           FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Syntax.Printer.fst"
                                                      (Prims.of_int (411))
                                                      (Prims.of_int (12))
                                                      (Prims.of_int (414))
                                                      (Prims.of_int (21)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Prims.fst"
                                                      (Prims.of_int (611))
                                                      (Prims.of_int (19))
                                                      (Prims.of_int (611))
                                                      (Prims.of_int (31)))))
                                             (Obj.magic uu___5)
                                             (fun uu___6 ->
                                                FStar_Tactics_Effect.lift_div_tac
                                                  (fun uu___7 ->
                                                     Prims.strcat
                                                       "rewrite each "
                                                       (Prims.strcat uu___6
                                                          ""))) in
                                         FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Syntax.Printer.fst"
                                                    (Prims.of_int (410))
                                                    (Prims.of_int (10))
                                                    (Prims.of_int (414))
                                                    (Prims.of_int (21)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Syntax.Printer.fst"
                                                    (Prims.of_int (410))
                                                    (Prims.of_int (10))
                                                    (Prims.of_int (417))
                                                    (Prims.of_int (60)))))
                                           (Obj.magic uu___4)
                                           (fun uu___5 ->
                                              (fun uu___5 ->
                                                 let uu___6 =
                                                   match goal with
                                                   | FStar_Pervasives_Native.None
                                                       ->
                                                       Obj.magic
                                                         (Obj.repr
                                                            (FStar_Tactics_Effect.lift_div_tac
                                                               (fun uu___7 ->
                                                                  "")))
                                                   | FStar_Pervasives_Native.Some
                                                       t2 ->
                                                       Obj.magic
                                                         (Obj.repr
                                                            (let uu___7 =
                                                               term_to_string
                                                                 t2 in
                                                             FStar_Tactics_Effect.tac_bind
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (417))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (417))
                                                                    (Prims.of_int (59)))))
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                               (Obj.magic
                                                                  uu___7)
                                                               (fun uu___8 ->
                                                                  FStar_Tactics_Effect.lift_div_tac
                                                                    (
                                                                    fun
                                                                    uu___9 ->
                                                                    Prims.strcat
                                                                    " in "
                                                                    (Prims.strcat
                                                                    uu___8 ""))))) in
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Syntax.Printer.fst"
                                                               (Prims.of_int (415))
                                                               (Prims.of_int (12))
                                                               (Prims.of_int (417))
                                                               (Prims.of_int (60)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Pulse.Syntax.Printer.fst"
                                                               (Prims.of_int (410))
                                                               (Prims.of_int (10))
                                                               (Prims.of_int (417))
                                                               (Prims.of_int (60)))))
                                                      (Obj.magic uu___6)
                                                      (fun uu___7 ->
                                                         FStar_Tactics_Effect.lift_div_tac
                                                           (fun uu___8 ->
                                                              (uu___5,
                                                                uu___7)))))
                                                uu___5)))
                               | Pulse_Syntax_Base.REWRITE
                                   { Pulse_Syntax_Base.t1 = t11;
                                     Pulse_Syntax_Base.t2 = t2;
                                     Pulse_Syntax_Base.tac_opt1 = uu___3;_}
                                   ->
                                   Obj.magic
                                     (Obj.repr
                                        (let uu___4 =
                                           let uu___5 = term_to_string t2 in
                                           FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Syntax.Printer.fst"
                                                      (Prims.of_int (419))
                                                      (Prims.of_int (57))
                                                      (Prims.of_int (419))
                                                      (Prims.of_int (76)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Syntax.Printer.fst"
                                                      (Prims.of_int (419))
                                                      (Prims.of_int (10))
                                                      (Prims.of_int (419))
                                                      (Prims.of_int (76)))))
                                             (Obj.magic uu___5)
                                             (fun uu___6 ->
                                                (fun uu___6 ->
                                                   let uu___7 =
                                                     let uu___8 =
                                                       term_to_string t11 in
                                                     FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "Pulse.Syntax.Printer.fst"
                                                                (Prims.of_int (419))
                                                                (Prims.of_int (37))
                                                                (Prims.of_int (419))
                                                                (Prims.of_int (56)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "FStar.Printf.fst"
                                                                (Prims.of_int (122))
                                                                (Prims.of_int (8))
                                                                (Prims.of_int (124))
                                                                (Prims.of_int (44)))))
                                                       (Obj.magic uu___8)
                                                       (fun uu___9 ->
                                                          FStar_Tactics_Effect.lift_div_tac
                                                            (fun uu___10 ->
                                                               fun x ->
                                                                 Prims.strcat
                                                                   (Prims.strcat
                                                                    "rewrite "
                                                                    (Prims.strcat
                                                                    uu___9
                                                                    " as "))
                                                                   (Prims.strcat
                                                                    x ""))) in
                                                   Obj.magic
                                                     (FStar_Tactics_Effect.tac_bind
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Syntax.Printer.fst"
                                                                 (Prims.of_int (419))
                                                                 (Prims.of_int (10))
                                                                 (Prims.of_int (419))
                                                                 (Prims.of_int (76)))))
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Pulse.Syntax.Printer.fst"
                                                                 (Prims.of_int (419))
                                                                 (Prims.of_int (10))
                                                                 (Prims.of_int (419))
                                                                 (Prims.of_int (76)))))
                                                        (Obj.magic uu___7)
                                                        (fun uu___8 ->
                                                           FStar_Tactics_Effect.lift_div_tac
                                                             (fun uu___9 ->
                                                                uu___8 uu___6))))
                                                  uu___6) in
                                         FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Syntax.Printer.fst"
                                                    (Prims.of_int (419))
                                                    (Prims.of_int (10))
                                                    (Prims.of_int (419))
                                                    (Prims.of_int (76)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Pulse.Syntax.Printer.fst"
                                                    (Prims.of_int (419))
                                                    (Prims.of_int (10))
                                                    (Prims.of_int (419))
                                                    (Prims.of_int (80)))))
                                           (Obj.magic uu___4)
                                           (fun uu___5 ->
                                              FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___6 -> (uu___5, "")))))
                               | Pulse_Syntax_Base.WILD ->
                                   Obj.magic
                                     (Obj.repr
                                        (FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___3 -> ("_", ""))))
                               | Pulse_Syntax_Base.SHOW_PROOF_STATE uu___3 ->
                                   Obj.magic
                                     (Obj.repr
                                        (FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___4 ->
                                              ("show_proof_state", "")))) in
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Syntax.Printer.fst"
                                           (Prims.of_int (405))
                                           (Prims.of_int (8))
                                           (Prims.of_int (421))
                                           (Prims.of_int (54)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Syntax.Printer.fst"
                                           (Prims.of_int (403))
                                           (Prims.of_int (8))
                                           (Prims.of_int (424))
                                           (Prims.of_int (36)))))
                                  (Obj.magic uu___2)
                                  (fun uu___3 ->
                                     (fun uu___3 ->
                                        match uu___3 with
                                        | (ht, p) ->
                                            let uu___4 =
                                              st_term_to_string' level t1 in
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Pulse.Syntax.Printer.fst"
                                                          (Prims.of_int (424))
                                                          (Prims.of_int (8))
                                                          (Prims.of_int (424))
                                                          (Prims.of_int (36)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "Prims.fst"
                                                          (Prims.of_int (611))
                                                          (Prims.of_int (19))
                                                          (Prims.of_int (611))
                                                          (Prims.of_int (31)))))
                                                 (Obj.magic uu___4)
                                                 (fun uu___5 ->
                                                    FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___6 ->
                                                         Prims.strcat
                                                           (Prims.strcat
                                                              (Prims.strcat
                                                                 (Prims.strcat
                                                                    ""
                                                                    (
                                                                    Prims.strcat
                                                                    with_prefix
                                                                    " "))
                                                                 (Prims.strcat
                                                                    ht " "))
                                                              (Prims.strcat p
                                                                 "; "))
                                                           (Prims.strcat
                                                              uu___5 "")))))
                                       uu___3))) uu___2))) uu___1)
      | Pulse_Syntax_Base.Tm_WithInv
          { Pulse_Syntax_Base.name1 = name; Pulse_Syntax_Base.body6 = body;
            Pulse_Syntax_Base.returns_inv = returns_inv;_}
          ->
          let uu___ =
            match returns_inv with
            | FStar_Pervasives_Native.None ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> "")))
            | FStar_Pervasives_Native.Some (b, t1, is) ->
                Obj.magic
                  (Obj.repr
                     (let uu___1 = term_to_string is in
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "Pulse.Syntax.Printer.fst"
                                 (Prims.of_int (436)) (Prims.of_int (12))
                                 (Prims.of_int (436)) (Prims.of_int (31)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "Pulse.Syntax.Printer.fst"
                                 (Prims.of_int (433)) (Prims.of_int (10))
                                 (Prims.of_int (436)) (Prims.of_int (31)))))
                        (Obj.magic uu___1)
                        (fun uu___2 ->
                           (fun uu___2 ->
                              let uu___3 =
                                let uu___4 = term_to_string t1 in
                                FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Syntax.Printer.fst"
                                           (Prims.of_int (435))
                                           (Prims.of_int (12))
                                           (Prims.of_int (435))
                                           (Prims.of_int (30)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "Pulse.Syntax.Printer.fst"
                                           (Prims.of_int (433))
                                           (Prims.of_int (10))
                                           (Prims.of_int (436))
                                           (Prims.of_int (31)))))
                                  (Obj.magic uu___4)
                                  (fun uu___5 ->
                                     (fun uu___5 ->
                                        let uu___6 =
                                          let uu___7 = binder_to_string b in
                                          FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Pulse.Syntax.Printer.fst"
                                                     (Prims.of_int (434))
                                                     (Prims.of_int (12))
                                                     (Prims.of_int (434))
                                                     (Prims.of_int (32)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "FStar.Printf.fst"
                                                     (Prims.of_int (122))
                                                     (Prims.of_int (8))
                                                     (Prims.of_int (124))
                                                     (Prims.of_int (44)))))
                                            (Obj.magic uu___7)
                                            (fun uu___8 ->
                                               FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___9 ->
                                                    fun x ->
                                                      fun x1 ->
                                                        Prims.strcat
                                                          (Prims.strcat
                                                             (Prims.strcat
                                                                "\nreturns "
                                                                (Prims.strcat
                                                                   uu___8
                                                                   "\nensures "))
                                                             (Prims.strcat x
                                                                "\nopens "))
                                                          (Prims.strcat x1 ""))) in
                                        Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Syntax.Printer.fst"
                                                      (Prims.of_int (433))
                                                      (Prims.of_int (10))
                                                      (Prims.of_int (436))
                                                      (Prims.of_int (31)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Pulse.Syntax.Printer.fst"
                                                      (Prims.of_int (433))
                                                      (Prims.of_int (10))
                                                      (Prims.of_int (436))
                                                      (Prims.of_int (31)))))
                                             (Obj.magic uu___6)
                                             (fun uu___7 ->
                                                FStar_Tactics_Effect.lift_div_tac
                                                  (fun uu___8 ->
                                                     uu___7 uu___5)))) uu___5) in
                              Obj.magic
                                (FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Syntax.Printer.fst"
                                            (Prims.of_int (433))
                                            (Prims.of_int (10))
                                            (Prims.of_int (436))
                                            (Prims.of_int (31)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "Pulse.Syntax.Printer.fst"
                                            (Prims.of_int (433))
                                            (Prims.of_int (10))
                                            (Prims.of_int (436))
                                            (Prims.of_int (31)))))
                                   (Obj.magic uu___3)
                                   (fun uu___4 ->
                                      FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___5 -> uu___4 uu___2))))
                             uu___2))) in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                     (Prims.of_int (430)) (Prims.of_int (8))
                     (Prims.of_int (436)) (Prims.of_int (32)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                     (Prims.of_int (427)) (Prims.of_int (6))
                     (Prims.of_int (436)) (Prims.of_int (32)))))
            (Obj.magic uu___)
            (fun uu___1 ->
               (fun uu___1 ->
                  let uu___2 =
                    let uu___3 = st_term_to_string' level body in
                    FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                               (Prims.of_int (429)) (Prims.of_int (8))
                               (Prims.of_int (429)) (Prims.of_int (39)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                               (Prims.of_int (427)) (Prims.of_int (6))
                               (Prims.of_int (436)) (Prims.of_int (32)))))
                      (Obj.magic uu___3)
                      (fun uu___4 ->
                         (fun uu___4 ->
                            let uu___5 =
                              let uu___6 = term_to_string name in
                              FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Syntax.Printer.fst"
                                         (Prims.of_int (428))
                                         (Prims.of_int (8))
                                         (Prims.of_int (428))
                                         (Prims.of_int (29)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Printf.fst"
                                         (Prims.of_int (122))
                                         (Prims.of_int (8))
                                         (Prims.of_int (124))
                                         (Prims.of_int (44)))))
                                (Obj.magic uu___6)
                                (fun uu___7 ->
                                   FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___8 ->
                                        fun x ->
                                          fun x1 ->
                                            Prims.strcat
                                              (Prims.strcat
                                                 (Prims.strcat "with_inv "
                                                    (Prims.strcat uu___7 " "))
                                                 (Prims.strcat x " "))
                                              (Prims.strcat x1 ""))) in
                            Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Syntax.Printer.fst"
                                          (Prims.of_int (427))
                                          (Prims.of_int (6))
                                          (Prims.of_int (436))
                                          (Prims.of_int (32)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Pulse.Syntax.Printer.fst"
                                          (Prims.of_int (427))
                                          (Prims.of_int (6))
                                          (Prims.of_int (436))
                                          (Prims.of_int (32)))))
                                 (Obj.magic uu___5)
                                 (fun uu___6 ->
                                    FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___7 -> uu___6 uu___4)))) uu___4) in
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                                (Prims.of_int (427)) (Prims.of_int (6))
                                (Prims.of_int (436)) (Prims.of_int (32)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                                (Prims.of_int (427)) (Prims.of_int (6))
                                (Prims.of_int (436)) (Prims.of_int (32)))))
                       (Obj.magic uu___2)
                       (fun uu___3 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___4 -> uu___3 uu___1)))) uu___1)
and (branches_to_string :
  (Pulse_Syntax_Base.pattern * Pulse_Syntax_Base.st_term) Prims.list ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    (fun brs ->
       match brs with
       | [] ->
           Obj.magic
             (Obj.repr (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> "")))
       | b::bs ->
           Obj.magic
             (Obj.repr
                (let uu___ = branch_to_string b in
                 FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                            (Prims.of_int (441)) (Prims.of_int (13))
                            (Prims.of_int (441)) (Prims.of_int (31)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                            (Prims.of_int (441)) (Prims.of_int (13))
                            (Prims.of_int (441)) (Prims.of_int (55)))))
                   (Obj.magic uu___)
                   (fun uu___1 ->
                      (fun uu___1 ->
                         let uu___2 = branches_to_string bs in
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Syntax.Printer.fst"
                                       (Prims.of_int (441))
                                       (Prims.of_int (34))
                                       (Prims.of_int (441))
                                       (Prims.of_int (55)))))
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
                                   (fun uu___4 -> Prims.strcat uu___1 uu___3))))
                        uu___1)))) uu___
and (branch_to_string :
  (Pulse_Syntax_Base.pattern * Pulse_Syntax_Base.st_term) ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun br ->
    let uu___ =
      Obj.magic (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> br)) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
               (Prims.of_int (444)) (Prims.of_int (17)) (Prims.of_int (444))
               (Prims.of_int (19)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
               (Prims.of_int (443)) (Prims.of_int (35)) (Prims.of_int (447))
               (Prims.of_int (29))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun uu___1 ->
            match uu___1 with
            | (pat, e) ->
                let uu___2 = st_term_to_string' "" e in
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                              (Prims.of_int (447)) (Prims.of_int (4))
                              (Prims.of_int (447)) (Prims.of_int (29)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                              (Prims.of_int (445)) (Prims.of_int (2))
                              (Prims.of_int (447)) (Prims.of_int (29)))))
                     (Obj.magic uu___2)
                     (fun uu___3 ->
                        (fun uu___3 ->
                           let uu___4 =
                             let uu___5 = pattern_to_string pat in
                             FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "Pulse.Syntax.Printer.fst"
                                        (Prims.of_int (446))
                                        (Prims.of_int (4))
                                        (Prims.of_int (446))
                                        (Prims.of_int (27)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range "FStar.Printf.fst"
                                        (Prims.of_int (122))
                                        (Prims.of_int (8))
                                        (Prims.of_int (124))
                                        (Prims.of_int (44)))))
                               (Obj.magic uu___5)
                               (fun uu___6 ->
                                  FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___7 ->
                                       fun x ->
                                         Prims.strcat
                                           (Prims.strcat "{ "
                                              (Prims.strcat uu___6 " -> "))
                                           (Prims.strcat x " }"))) in
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Syntax.Printer.fst"
                                         (Prims.of_int (445))
                                         (Prims.of_int (2))
                                         (Prims.of_int (447))
                                         (Prims.of_int (29)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Pulse.Syntax.Printer.fst"
                                         (Prims.of_int (445))
                                         (Prims.of_int (2))
                                         (Prims.of_int (447))
                                         (Prims.of_int (29)))))
                                (Obj.magic uu___4)
                                (fun uu___5 ->
                                   FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___6 -> uu___5 uu___3)))) uu___3)))
           uu___1)
and (pattern_to_string :
  Pulse_Syntax_Base.pattern ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    (fun p ->
       match p with
       | Pulse_Syntax_Base.Pat_Cons (fv, pats) ->
           Obj.magic
             (Obj.repr
                (let uu___ =
                   let uu___1 =
                     FStar_Tactics_Util.map
                       (fun uu___2 ->
                          match uu___2 with
                          | (p1, uu___3) -> pattern_to_string p1) pats in
                   FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                              (Prims.of_int (454)) (Prims.of_int (25))
                              (Prims.of_int (454)) (Prims.of_int (73)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                              (Prims.of_int (454)) (Prims.of_int (6))
                              (Prims.of_int (454)) (Prims.of_int (74)))))
                     (Obj.magic uu___1)
                     (fun uu___2 ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___3 -> FStar_String.concat " " uu___2)) in
                 FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                            (Prims.of_int (454)) (Prims.of_int (6))
                            (Prims.of_int (454)) (Prims.of_int (74)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Prims.fst"
                            (Prims.of_int (611)) (Prims.of_int (19))
                            (Prims.of_int (611)) (Prims.of_int (31)))))
                   (Obj.magic uu___)
                   (fun uu___1 ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___2 ->
                           Prims.strcat
                             (Prims.strcat "("
                                (Prims.strcat
                                   (FStar_String.concat "."
                                      fv.Pulse_Syntax_Base.fv_name) " "))
                             (Prims.strcat uu___1 ")")))))
       | Pulse_Syntax_Base.Pat_Constant c ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___ -> "<constant>")))
       | Pulse_Syntax_Base.Pat_Var (x, uu___) ->
           Obj.magic (Obj.repr (FStar_Tactics_Unseal.unseal x))
       | Pulse_Syntax_Base.Pat_Dot_Term (FStar_Pervasives_Native.None) ->
           Obj.magic
             (Obj.repr (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> "")))
       | Pulse_Syntax_Base.Pat_Dot_Term (FStar_Pervasives_Native.Some t) ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> "(.??)"))))
      uu___
let (st_term_to_string :
  Pulse_Syntax_Base.st_term ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  = fun t -> st_term_to_string' "" t
let (tag_of_term : Pulse_Syntax_Base.term -> Prims.string) =
  fun t ->
    match Pulse_Syntax_Pure.inspect_term t with
    | Pulse_Syntax_Pure.Tm_Emp -> "Tm_Emp"
    | Pulse_Syntax_Pure.Tm_Pure uu___ -> "Tm_Pure"
    | Pulse_Syntax_Pure.Tm_Star (uu___, uu___1) -> "Tm_Star"
    | Pulse_Syntax_Pure.Tm_ExistsSL (uu___, uu___1, uu___2) -> "Tm_ExistsSL"
    | Pulse_Syntax_Pure.Tm_ForallSL (uu___, uu___1, uu___2) -> "Tm_ForallSL"
    | Pulse_Syntax_Pure.Tm_SLProp -> "Tm_SLProp"
    | Pulse_Syntax_Pure.Tm_Inames -> "Tm_Inames"
    | Pulse_Syntax_Pure.Tm_EmpInames -> "Tm_EmpInames"
    | Pulse_Syntax_Pure.Tm_Unknown -> "Tm_Unknown"
    | Pulse_Syntax_Pure.Tm_Inv (uu___, uu___1) -> "Tm_Inv"
    | Pulse_Syntax_Pure.Tm_FStar uu___ -> "Tm_FStar"
let (tag_of_st_term : Pulse_Syntax_Base.st_term -> Prims.string) =
  fun t ->
    match t.Pulse_Syntax_Base.term1 with
    | Pulse_Syntax_Base.Tm_Return uu___ -> "Tm_Return"
    | Pulse_Syntax_Base.Tm_Abs uu___ -> "Tm_Abs"
    | Pulse_Syntax_Base.Tm_STApp uu___ -> "Tm_STApp"
    | Pulse_Syntax_Base.Tm_Bind uu___ -> "Tm_Bind"
    | Pulse_Syntax_Base.Tm_TotBind uu___ -> "Tm_TotBind"
    | Pulse_Syntax_Base.Tm_If uu___ -> "Tm_If"
    | Pulse_Syntax_Base.Tm_Match uu___ -> "Tm_Match"
    | Pulse_Syntax_Base.Tm_IntroPure uu___ -> "Tm_IntroPure"
    | Pulse_Syntax_Base.Tm_ElimExists uu___ -> "Tm_ElimExists"
    | Pulse_Syntax_Base.Tm_IntroExists uu___ -> "Tm_IntroExists"
    | Pulse_Syntax_Base.Tm_While uu___ -> "Tm_While"
    | Pulse_Syntax_Base.Tm_Par uu___ -> "Tm_Par"
    | Pulse_Syntax_Base.Tm_WithLocal uu___ -> "Tm_WithLocal"
    | Pulse_Syntax_Base.Tm_WithLocalArray uu___ -> "Tm_WithLocalArray"
    | Pulse_Syntax_Base.Tm_Rewrite uu___ -> "Tm_Rewrite"
    | Pulse_Syntax_Base.Tm_Admit uu___ -> "Tm_Admit"
    | Pulse_Syntax_Base.Tm_Unreachable uu___ -> "Tm_Unreachable"
    | Pulse_Syntax_Base.Tm_ProofHintWithBinders uu___ ->
        "Tm_ProofHintWithBinders"
    | Pulse_Syntax_Base.Tm_WithInv uu___ -> "Tm_WithInv"
let (tag_of_comp :
  Pulse_Syntax_Base.comp ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    (fun c ->
       match c with
       | Pulse_Syntax_Base.C_Tot uu___ ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> "Total")))
       | Pulse_Syntax_Base.C_ST uu___ ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> "ST")))
       | Pulse_Syntax_Base.C_STAtomic (i, obs, uu___) ->
           Obj.magic
             (Obj.repr
                (let uu___1 = term_to_string i in
                 FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                            (Prims.of_int (509)) (Prims.of_int (57))
                            (Prims.of_int (509)) (Prims.of_int (75)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Prims.fst"
                            (Prims.of_int (611)) (Prims.of_int (19))
                            (Prims.of_int (611)) (Prims.of_int (31)))))
                   (Obj.magic uu___1)
                   (fun uu___2 ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___3 ->
                           Prims.strcat
                             (Prims.strcat ""
                                (Prims.strcat (observability_to_string obs)
                                   " ")) (Prims.strcat uu___2 "")))))
       | Pulse_Syntax_Base.C_STGhost (uu___, uu___1) ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> "Ghost"))))
      uu___
let rec (print_st_head : Pulse_Syntax_Base.st_term -> Prims.string) =
  fun t ->
    match t.Pulse_Syntax_Base.term1 with
    | Pulse_Syntax_Base.Tm_Abs uu___ -> "Abs"
    | Pulse_Syntax_Base.Tm_Return p -> print_head p.Pulse_Syntax_Base.term
    | Pulse_Syntax_Base.Tm_Bind uu___ -> "Bind"
    | Pulse_Syntax_Base.Tm_TotBind uu___ -> "TotBind"
    | Pulse_Syntax_Base.Tm_If uu___ -> "If"
    | Pulse_Syntax_Base.Tm_Match uu___ -> "Match"
    | Pulse_Syntax_Base.Tm_While uu___ -> "While"
    | Pulse_Syntax_Base.Tm_Admit uu___ -> "Admit"
    | Pulse_Syntax_Base.Tm_Unreachable uu___ -> "Unreachable"
    | Pulse_Syntax_Base.Tm_Par uu___ -> "Par"
    | Pulse_Syntax_Base.Tm_Rewrite uu___ -> "Rewrite"
    | Pulse_Syntax_Base.Tm_WithLocal uu___ -> "WithLocal"
    | Pulse_Syntax_Base.Tm_WithLocalArray uu___ -> "WithLocalArray"
    | Pulse_Syntax_Base.Tm_STApp
        { Pulse_Syntax_Base.head = p; Pulse_Syntax_Base.arg_qual = uu___;
          Pulse_Syntax_Base.arg = uu___1;_}
        -> print_head p
    | Pulse_Syntax_Base.Tm_IntroPure uu___ -> "IntroPure"
    | Pulse_Syntax_Base.Tm_IntroExists uu___ -> "IntroExists"
    | Pulse_Syntax_Base.Tm_ElimExists uu___ -> "ElimExists"
    | Pulse_Syntax_Base.Tm_ProofHintWithBinders uu___ -> "AssertWithBinders"
    | Pulse_Syntax_Base.Tm_WithInv uu___ -> "WithInv"
and (print_head : Pulse_Syntax_Base.term -> Prims.string) =
  fun t -> "<pure term>"
let rec (print_skel : Pulse_Syntax_Base.st_term -> Prims.string) =
  fun t ->
    match t.Pulse_Syntax_Base.term1 with
    | Pulse_Syntax_Base.Tm_Abs
        { Pulse_Syntax_Base.b = uu___; Pulse_Syntax_Base.q = uu___1;
          Pulse_Syntax_Base.ascription = uu___2;
          Pulse_Syntax_Base.body = body;_}
        -> Prims.strcat "(fun _ -> " (Prims.strcat (print_skel body) ")")
    | Pulse_Syntax_Base.Tm_Return
        { Pulse_Syntax_Base.expected_type = uu___;
          Pulse_Syntax_Base.insert_eq = uu___1; Pulse_Syntax_Base.term = p;_}
        -> print_head p
    | Pulse_Syntax_Base.Tm_Bind
        { Pulse_Syntax_Base.binder = uu___; Pulse_Syntax_Base.head1 = e1;
          Pulse_Syntax_Base.body1 = e2;_}
        ->
        Prims.strcat
          (Prims.strcat "(Bind " (Prims.strcat (print_skel e1) " "))
          (Prims.strcat (print_skel e2) ")")
    | Pulse_Syntax_Base.Tm_TotBind
        { Pulse_Syntax_Base.binder1 = uu___;
          Pulse_Syntax_Base.head2 = uu___1; Pulse_Syntax_Base.body2 = e2;_}
        -> Prims.strcat "(TotBind _ " (Prims.strcat (print_skel e2) ")")
    | Pulse_Syntax_Base.Tm_If uu___ -> "If"
    | Pulse_Syntax_Base.Tm_Match uu___ -> "Match"
    | Pulse_Syntax_Base.Tm_While uu___ -> "While"
    | Pulse_Syntax_Base.Tm_Admit uu___ -> "Admit"
    | Pulse_Syntax_Base.Tm_Unreachable uu___ -> "Unreachable"
    | Pulse_Syntax_Base.Tm_Par uu___ -> "Par"
    | Pulse_Syntax_Base.Tm_Rewrite uu___ -> "Rewrite"
    | Pulse_Syntax_Base.Tm_WithLocal uu___ -> "WithLocal"
    | Pulse_Syntax_Base.Tm_WithLocalArray uu___ -> "WithLocalArray"
    | Pulse_Syntax_Base.Tm_STApp
        { Pulse_Syntax_Base.head = p; Pulse_Syntax_Base.arg_qual = uu___;
          Pulse_Syntax_Base.arg = uu___1;_}
        -> print_head p
    | Pulse_Syntax_Base.Tm_IntroPure uu___ -> "IntroPure"
    | Pulse_Syntax_Base.Tm_IntroExists uu___ -> "IntroExists"
    | Pulse_Syntax_Base.Tm_ElimExists uu___ -> "ElimExists"
    | Pulse_Syntax_Base.Tm_ProofHintWithBinders uu___ -> "AssertWithBinders"
    | Pulse_Syntax_Base.Tm_WithInv uu___ -> "WithInv"
let (decl_to_string :
  Pulse_Syntax_Base.decl ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun d ->
    match d.Pulse_Syntax_Base.d with
    | Pulse_Syntax_Base.FnDefn
        { Pulse_Syntax_Base.id = id; Pulse_Syntax_Base.isrec = isrec;
          Pulse_Syntax_Base.bs = bs; Pulse_Syntax_Base.comp = uu___;
          Pulse_Syntax_Base.meas = uu___1; Pulse_Syntax_Base.body7 = body;_}
        ->
        let uu___2 =
          let uu___3 =
            let uu___4 =
              let uu___5 =
                let uu___6 =
                  let uu___7 =
                    FStar_Tactics_Util.map
                      (fun uu___8 ->
                         match uu___8 with
                         | (uu___9, b, uu___10) -> binder_to_string b) bs in
                  FStar_Tactics_Effect.tac_bind
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                             (Prims.of_int (570)) (Prims.of_int (23))
                             (Prims.of_int (570)) (Prims.of_int (71)))))
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                             (Prims.of_int (570)) (Prims.of_int (5))
                             (Prims.of_int (570)) (Prims.of_int (71)))))
                    (Obj.magic uu___7)
                    (fun uu___8 ->
                       FStar_Tactics_Effect.lift_div_tac
                         (fun uu___9 -> FStar_String.concat " " uu___8)) in
                FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                           (Prims.of_int (570)) (Prims.of_int (5))
                           (Prims.of_int (570)) (Prims.of_int (71)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                           (Prims.of_int (570)) (Prims.of_int (5))
                           (Prims.of_int (571)) (Prims.of_int (42)))))
                  (Obj.magic uu___6)
                  (fun uu___7 ->
                     (fun uu___7 ->
                        let uu___8 =
                          let uu___9 =
                            let uu___10 = st_term_to_string body in
                            FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Pulse.Syntax.Printer.fst"
                                       (Prims.of_int (571))
                                       (Prims.of_int (14))
                                       (Prims.of_int (571))
                                       (Prims.of_int (36)))))
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
                                   (fun uu___12 -> Prims.strcat uu___11 "}")) in
                          FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "Pulse.Syntax.Printer.fst"
                                     (Prims.of_int (571)) (Prims.of_int (14))
                                     (Prims.of_int (571)) (Prims.of_int (42)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range "Prims.fst"
                                     (Prims.of_int (611)) (Prims.of_int (19))
                                     (Prims.of_int (611)) (Prims.of_int (31)))))
                            (Obj.magic uu___9)
                            (fun uu___10 ->
                               FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___11 -> Prims.strcat " { " uu___10)) in
                        Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "Pulse.Syntax.Printer.fst"
                                      (Prims.of_int (571)) (Prims.of_int (6))
                                      (Prims.of_int (571))
                                      (Prims.of_int (42)))))
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
                                  (fun uu___10 -> Prims.strcat uu___7 uu___9))))
                       uu___7) in
              FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                         (Prims.of_int (570)) (Prims.of_int (5))
                         (Prims.of_int (571)) (Prims.of_int (42)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Prims.fst" (Prims.of_int (611))
                         (Prims.of_int (19)) (Prims.of_int (611))
                         (Prims.of_int (31))))) (Obj.magic uu___5)
                (fun uu___6 ->
                   FStar_Tactics_Effect.lift_div_tac
                     (fun uu___7 -> Prims.strcat " " uu___6)) in
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                       (Prims.of_int (569)) (Prims.of_int (32))
                       (Prims.of_int (571)) (Prims.of_int (42)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Prims.fst" (Prims.of_int (611))
                       (Prims.of_int (19)) (Prims.of_int (611))
                       (Prims.of_int (31))))) (Obj.magic uu___4)
              (fun uu___5 ->
                 FStar_Tactics_Effect.lift_div_tac
                   (fun uu___6 ->
                      Prims.strcat
                        (FStar_Pervasives_Native.fst
                           (FStar_Reflection_V2_Builtins.inspect_ident id))
                        uu___5)) in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                     (Prims.of_int (569)) (Prims.of_int (5))
                     (Prims.of_int (571)) (Prims.of_int (42)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Prims.fst" (Prims.of_int (611))
                     (Prims.of_int (19)) (Prims.of_int (611))
                     (Prims.of_int (31))))) (Obj.magic uu___3)
            (fun uu___4 ->
               FStar_Tactics_Effect.lift_div_tac
                 (fun uu___5 ->
                    Prims.strcat (if isrec then "rec " else "") uu___4)) in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                   (Prims.of_int (568)) (Prims.of_int (12))
                   (Prims.of_int (571)) (Prims.of_int (42)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Prims.fst" (Prims.of_int (611))
                   (Prims.of_int (19)) (Prims.of_int (611))
                   (Prims.of_int (31))))) (Obj.magic uu___2)
          (fun uu___3 ->
             FStar_Tactics_Effect.lift_div_tac
               (fun uu___4 -> Prims.strcat "fn " uu___3))
    | Pulse_Syntax_Base.FnDecl
        { Pulse_Syntax_Base.id1 = id; Pulse_Syntax_Base.bs1 = bs;
          Pulse_Syntax_Base.comp1 = uu___;_}
        ->
        let uu___1 =
          let uu___2 =
            let uu___3 =
              let uu___4 =
                FStar_Tactics_Util.map
                  (fun uu___5 ->
                     match uu___5 with
                     | (uu___6, b, uu___7) -> binder_to_string b) bs in
              FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                         (Prims.of_int (575)) (Prims.of_int (22))
                         (Prims.of_int (575)) (Prims.of_int (70)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                         (Prims.of_int (575)) (Prims.of_int (4))
                         (Prims.of_int (575)) (Prims.of_int (70)))))
                (Obj.magic uu___4)
                (fun uu___5 ->
                   FStar_Tactics_Effect.lift_div_tac
                     (fun uu___6 -> FStar_String.concat " " uu___5)) in
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                       (Prims.of_int (575)) (Prims.of_int (4))
                       (Prims.of_int (575)) (Prims.of_int (70)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Prims.fst" (Prims.of_int (611))
                       (Prims.of_int (19)) (Prims.of_int (611))
                       (Prims.of_int (31))))) (Obj.magic uu___3)
              (fun uu___4 ->
                 FStar_Tactics_Effect.lift_div_tac
                   (fun uu___5 -> Prims.strcat " " uu___4)) in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                     (Prims.of_int (574)) (Prims.of_int (31))
                     (Prims.of_int (575)) (Prims.of_int (70)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Prims.fst" (Prims.of_int (611))
                     (Prims.of_int (19)) (Prims.of_int (611))
                     (Prims.of_int (31))))) (Obj.magic uu___2)
            (fun uu___3 ->
               FStar_Tactics_Effect.lift_div_tac
                 (fun uu___4 ->
                    Prims.strcat
                      (FStar_Pervasives_Native.fst
                         (FStar_Reflection_V2_Builtins.inspect_ident id))
                      uu___3)) in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                   (Prims.of_int (574)) (Prims.of_int (4))
                   (Prims.of_int (575)) (Prims.of_int (70)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Prims.fst" (Prims.of_int (611))
                   (Prims.of_int (19)) (Prims.of_int (611))
                   (Prims.of_int (31))))) (Obj.magic uu___1)
          (fun uu___2 ->
             FStar_Tactics_Effect.lift_div_tac
               (fun uu___3 -> Prims.strcat "fn " uu___2))