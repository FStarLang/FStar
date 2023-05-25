open Prims
let (name_to_string : FStar_Reflection_Types.name -> Prims.string) =
  fun f -> FStar_String.concat "." f
let (dbg_printing : Prims.bool) = true
let rec (universe_to_string :
  Prims.nat -> Pulse_Syntax_Base.universe -> Prims.string) =
  fun n ->
    fun u ->
      match FStar_Reflection_Builtins.inspect_universe u with
      | FStar_Reflection_Data.Uv_Unk -> "_"
      | FStar_Reflection_Data.Uv_Zero ->
          Prims.strcat "" (Prims.strcat (Prims.string_of_int n) "")
      | FStar_Reflection_Data.Uv_Succ u1 ->
          universe_to_string (n + Prims.int_one) u1
      | FStar_Reflection_Data.Uv_BVar x ->
          if n = Prims.int_zero
          then Prims.strcat "" (Prims.strcat (Prims.string_of_int x) "")
          else
            Prims.strcat
              (Prims.strcat "(" (Prims.strcat (Prims.string_of_int x) " + "))
              (Prims.strcat (Prims.string_of_int n) ")")
      | FStar_Reflection_Data.Uv_Max us ->
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
let rec (term_to_string :
  Pulse_Syntax_Base.term ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    (fun t ->
       match t with
       | Pulse_Syntax_Base.Tm_Emp ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> "emp")))
       | Pulse_Syntax_Base.Tm_Pure p ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                      (Prims.of_int (69)) (Prims.of_int (40))
                      (Prims.of_int (69)) (Prims.of_int (58)))
                   (FStar_Range.mk_range "prims.fst" (Prims.of_int (590))
                      (Prims.of_int (19)) (Prims.of_int (590))
                      (Prims.of_int (31))) (Obj.magic (term_to_string p))
                   (fun uu___ ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___1 ->
                           Prims.strcat "tm_pure " (Prims.strcat uu___ "")))))
       | Pulse_Syntax_Base.Tm_Star (p1, p2) ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                      (Prims.of_int (72)) (Prims.of_int (26))
                      (Prims.of_int (72)) (Prims.of_int (45)))
                   (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                      (Prims.of_int (71)) (Prims.of_int (6))
                      (Prims.of_int (72)) (Prims.of_int (45)))
                   (Obj.magic (term_to_string p2))
                   (fun uu___ ->
                      (fun uu___ ->
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Range.mk_range
                                 "Pulse.Syntax.Printer.fst"
                                 (Prims.of_int (71)) (Prims.of_int (6))
                                 (Prims.of_int (72)) (Prims.of_int (45)))
                              (FStar_Range.mk_range
                                 "Pulse.Syntax.Printer.fst"
                                 (Prims.of_int (71)) (Prims.of_int (6))
                                 (Prims.of_int (72)) (Prims.of_int (45)))
                              (Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Range.mk_range
                                       "Pulse.Syntax.Printer.fst"
                                       (Prims.of_int (71))
                                       (Prims.of_int (26))
                                       (Prims.of_int (71))
                                       (Prims.of_int (45)))
                                    (FStar_Range.mk_range "FStar.Printf.fst"
                                       (Prims.of_int (121))
                                       (Prims.of_int (8))
                                       (Prims.of_int (123))
                                       (Prims.of_int (44)))
                                    (Obj.magic (term_to_string p1))
                                    (fun uu___1 ->
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___2 ->
                                            fun x ->
                                              Prims.strcat
                                                (Prims.strcat "("
                                                   (Prims.strcat uu___1 " * "))
                                                (Prims.strcat x ")")))))
                              (fun uu___1 ->
                                 FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___2 -> uu___1 uu___)))) uu___)))
       | Pulse_Syntax_Base.Tm_ExistsSL (u, t1, body, uu___) ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                      (Prims.of_int (78)) (Prims.of_int (14))
                      (Prims.of_int (78)) (Prims.of_int (35)))
                   (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                      (Prims.of_int (75)) (Prims.of_int (6))
                      (Prims.of_int (78)) (Prims.of_int (35)))
                   (Obj.magic (term_to_string body))
                   (fun uu___1 ->
                      (fun uu___1 ->
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Range.mk_range
                                 "Pulse.Syntax.Printer.fst"
                                 (Prims.of_int (75)) (Prims.of_int (6))
                                 (Prims.of_int (78)) (Prims.of_int (35)))
                              (FStar_Range.mk_range
                                 "Pulse.Syntax.Printer.fst"
                                 (Prims.of_int (75)) (Prims.of_int (6))
                                 (Prims.of_int (78)) (Prims.of_int (35)))
                              (Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Range.mk_range
                                       "Pulse.Syntax.Printer.fst"
                                       (Prims.of_int (77))
                                       (Prims.of_int (14))
                                       (Prims.of_int (77))
                                       (Prims.of_int (32)))
                                    (FStar_Range.mk_range "FStar.Printf.fst"
                                       (Prims.of_int (121))
                                       (Prims.of_int (8))
                                       (Prims.of_int (123))
                                       (Prims.of_int (44)))
                                    (Obj.magic (term_to_string t1))
                                    (fun uu___2 ->
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___3 ->
                                            fun x ->
                                              Prims.strcat
                                                (Prims.strcat
                                                   (Prims.strcat "(exists<"
                                                      (Prims.strcat
                                                         (universe_to_string
                                                            Prims.int_zero u)
                                                         "> (_:"))
                                                   (Prims.strcat uu___2 "). "))
                                                (Prims.strcat x ")")))))
                              (fun uu___2 ->
                                 FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___3 -> uu___2 uu___1)))) uu___1)))
       | Pulse_Syntax_Base.Tm_ForallSL (u, t1, body) ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                      (Prims.of_int (84)) (Prims.of_int (14))
                      (Prims.of_int (84)) (Prims.of_int (35)))
                   (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                      (Prims.of_int (81)) (Prims.of_int (6))
                      (Prims.of_int (84)) (Prims.of_int (35)))
                   (Obj.magic (term_to_string body))
                   (fun uu___ ->
                      (fun uu___ ->
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Range.mk_range
                                 "Pulse.Syntax.Printer.fst"
                                 (Prims.of_int (81)) (Prims.of_int (6))
                                 (Prims.of_int (84)) (Prims.of_int (35)))
                              (FStar_Range.mk_range
                                 "Pulse.Syntax.Printer.fst"
                                 (Prims.of_int (81)) (Prims.of_int (6))
                                 (Prims.of_int (84)) (Prims.of_int (35)))
                              (Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Range.mk_range
                                       "Pulse.Syntax.Printer.fst"
                                       (Prims.of_int (83))
                                       (Prims.of_int (14))
                                       (Prims.of_int (83))
                                       (Prims.of_int (32)))
                                    (FStar_Range.mk_range "FStar.Printf.fst"
                                       (Prims.of_int (121))
                                       (Prims.of_int (8))
                                       (Prims.of_int (123))
                                       (Prims.of_int (44)))
                                    (Obj.magic (term_to_string t1))
                                    (fun uu___1 ->
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___2 ->
                                            fun x ->
                                              Prims.strcat
                                                (Prims.strcat
                                                   (Prims.strcat "(forall<"
                                                      (Prims.strcat
                                                         (universe_to_string
                                                            Prims.int_zero u)
                                                         "> (_:"))
                                                   (Prims.strcat uu___1 "). "))
                                                (Prims.strcat x ")")))))
                              (fun uu___1 ->
                                 FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___2 -> uu___1 uu___)))) uu___)))
       | Pulse_Syntax_Base.Tm_VProp ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> "vprop")))
       | Pulse_Syntax_Base.Tm_Inames ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> "inames")))
       | Pulse_Syntax_Base.Tm_EmpInames ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___ -> "emp_inames")))
       | Pulse_Syntax_Base.Tm_Unknown ->
           Obj.magic
             (Obj.repr (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> "_")))
       | Pulse_Syntax_Base.Tm_FStar (t1, uu___) ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                      (Prims.of_int (105)) (Prims.of_int (34))
                      (Prims.of_int (105)) (Prims.of_int (54)))
                   (FStar_Range.mk_range "prims.fst" (Prims.of_int (590))
                      (Prims.of_int (19)) (Prims.of_int (590))
                      (Prims.of_int (31)))
                   (Obj.magic (FStar_Tactics_Builtins.term_to_string t1))
                   (fun uu___1 ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___2 ->
                           Prims.strcat "((tm_fstar) ("
                             (Prims.strcat uu___1 "))")))))) uu___
let (binder_to_string :
  Pulse_Syntax_Base.binder ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun b ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Range.mk_range "Pulse.Syntax.Printer.fst" (Prims.of_int (111))
         (Prims.of_int (12)) (Prims.of_int (111)) (Prims.of_int (40)))
      (FStar_Range.mk_range "Pulse.Syntax.Printer.fst" (Prims.of_int (109))
         (Prims.of_int (4)) (Prims.of_int (111)) (Prims.of_int (40)))
      (Obj.magic (term_to_string b.Pulse_Syntax_Base.binder_ty))
      (fun uu___ ->
         (fun uu___ ->
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                    (Prims.of_int (109)) (Prims.of_int (4))
                    (Prims.of_int (111)) (Prims.of_int (40)))
                 (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                    (Prims.of_int (109)) (Prims.of_int (4))
                    (Prims.of_int (111)) (Prims.of_int (40)))
                 (Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                          (Prims.of_int (110)) (Prims.of_int (12))
                          (Prims.of_int (110)) (Prims.of_int (38)))
                       (FStar_Range.mk_range "FStar.Printf.fst"
                          (Prims.of_int (121)) (Prims.of_int (8))
                          (Prims.of_int (123)) (Prims.of_int (44)))
                       (Obj.magic
                          (FStar_Tactics_Builtins.unseal
                             b.Pulse_Syntax_Base.binder_ppname))
                       (fun uu___1 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___2 ->
                               fun x ->
                                 Prims.strcat
                                   (Prims.strcat "" (Prims.strcat uu___1 ":"))
                                   (Prims.strcat x "")))))
                 (fun uu___1 ->
                    FStar_Tactics_Effect.lift_div_tac
                      (fun uu___2 -> uu___1 uu___)))) uu___)
let (comp_to_string :
  Pulse_Syntax_Base.comp ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun c ->
    match c with
    | Pulse_Syntax_Base.C_Tot t ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
             (Prims.of_int (117)) (Prims.of_int (23)) (Prims.of_int (117))
             (Prims.of_int (41)))
          (FStar_Range.mk_range "prims.fst" (Prims.of_int (590))
             (Prims.of_int (19)) (Prims.of_int (590)) (Prims.of_int (31)))
          (Obj.magic (term_to_string t))
          (fun uu___ ->
             FStar_Tactics_Effect.lift_div_tac
               (fun uu___1 -> Prims.strcat "Tot " (Prims.strcat uu___ "")))
    | Pulse_Syntax_Base.C_ST s ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
             (Prims.of_int (123)) (Prims.of_int (14)) (Prims.of_int (123))
             (Prims.of_int (37)))
          (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
             (Prims.of_int (120)) (Prims.of_int (6)) (Prims.of_int (123))
             (Prims.of_int (37)))
          (Obj.magic (term_to_string s.Pulse_Syntax_Base.post))
          (fun uu___ ->
             (fun uu___ ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                        (Prims.of_int (120)) (Prims.of_int (6))
                        (Prims.of_int (123)) (Prims.of_int (37)))
                     (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                        (Prims.of_int (120)) (Prims.of_int (6))
                        (Prims.of_int (123)) (Prims.of_int (37)))
                     (Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                              (Prims.of_int (122)) (Prims.of_int (14))
                              (Prims.of_int (122)) (Prims.of_int (36)))
                           (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                              (Prims.of_int (120)) (Prims.of_int (6))
                              (Prims.of_int (123)) (Prims.of_int (37)))
                           (Obj.magic
                              (term_to_string s.Pulse_Syntax_Base.pre))
                           (fun uu___1 ->
                              (fun uu___1 ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Range.mk_range
                                         "Pulse.Syntax.Printer.fst"
                                         (Prims.of_int (120))
                                         (Prims.of_int (6))
                                         (Prims.of_int (123))
                                         (Prims.of_int (37)))
                                      (FStar_Range.mk_range
                                         "Pulse.Syntax.Printer.fst"
                                         (Prims.of_int (120))
                                         (Prims.of_int (6))
                                         (Prims.of_int (123))
                                         (Prims.of_int (37)))
                                      (Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Range.mk_range
                                               "Pulse.Syntax.Printer.fst"
                                               (Prims.of_int (121))
                                               (Prims.of_int (14))
                                               (Prims.of_int (121))
                                               (Prims.of_int (36)))
                                            (FStar_Range.mk_range
                                               "FStar.Printf.fst"
                                               (Prims.of_int (121))
                                               (Prims.of_int (8))
                                               (Prims.of_int (123))
                                               (Prims.of_int (44)))
                                            (Obj.magic
                                               (term_to_string
                                                  s.Pulse_Syntax_Base.res))
                                            (fun uu___2 ->
                                               FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___3 ->
                                                    fun x ->
                                                      fun x1 ->
                                                        Prims.strcat
                                                          (Prims.strcat
                                                             (Prims.strcat
                                                                "ST "
                                                                (Prims.strcat
                                                                   uu___2 " "))
                                                             (Prims.strcat x
                                                                " "))
                                                          (Prims.strcat x1 "")))))
                                      (fun uu___2 ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___3 -> uu___2 uu___1))))
                                uu___1)))
                     (fun uu___1 ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___2 -> uu___1 uu___)))) uu___)
    | Pulse_Syntax_Base.C_STAtomic (inames, s) ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
             (Prims.of_int (130)) (Prims.of_int (14)) (Prims.of_int (130))
             (Prims.of_int (37)))
          (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
             (Prims.of_int (126)) (Prims.of_int (6)) (Prims.of_int (130))
             (Prims.of_int (37)))
          (Obj.magic (term_to_string s.Pulse_Syntax_Base.post))
          (fun uu___ ->
             (fun uu___ ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                        (Prims.of_int (126)) (Prims.of_int (6))
                        (Prims.of_int (130)) (Prims.of_int (37)))
                     (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                        (Prims.of_int (126)) (Prims.of_int (6))
                        (Prims.of_int (130)) (Prims.of_int (37)))
                     (Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                              (Prims.of_int (129)) (Prims.of_int (14))
                              (Prims.of_int (129)) (Prims.of_int (36)))
                           (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                              (Prims.of_int (126)) (Prims.of_int (6))
                              (Prims.of_int (130)) (Prims.of_int (37)))
                           (Obj.magic
                              (term_to_string s.Pulse_Syntax_Base.pre))
                           (fun uu___1 ->
                              (fun uu___1 ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Range.mk_range
                                         "Pulse.Syntax.Printer.fst"
                                         (Prims.of_int (126))
                                         (Prims.of_int (6))
                                         (Prims.of_int (130))
                                         (Prims.of_int (37)))
                                      (FStar_Range.mk_range
                                         "Pulse.Syntax.Printer.fst"
                                         (Prims.of_int (126))
                                         (Prims.of_int (6))
                                         (Prims.of_int (130))
                                         (Prims.of_int (37)))
                                      (Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Range.mk_range
                                               "Pulse.Syntax.Printer.fst"
                                               (Prims.of_int (128))
                                               (Prims.of_int (14))
                                               (Prims.of_int (128))
                                               (Prims.of_int (36)))
                                            (FStar_Range.mk_range
                                               "Pulse.Syntax.Printer.fst"
                                               (Prims.of_int (126))
                                               (Prims.of_int (6))
                                               (Prims.of_int (130))
                                               (Prims.of_int (37)))
                                            (Obj.magic
                                               (term_to_string
                                                  s.Pulse_Syntax_Base.res))
                                            (fun uu___2 ->
                                               (fun uu___2 ->
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Range.mk_range
                                                          "Pulse.Syntax.Printer.fst"
                                                          (Prims.of_int (126))
                                                          (Prims.of_int (6))
                                                          (Prims.of_int (130))
                                                          (Prims.of_int (37)))
                                                       (FStar_Range.mk_range
                                                          "Pulse.Syntax.Printer.fst"
                                                          (Prims.of_int (126))
                                                          (Prims.of_int (6))
                                                          (Prims.of_int (130))
                                                          (Prims.of_int (37)))
                                                       (Obj.magic
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (FStar_Range.mk_range
                                                                "Pulse.Syntax.Printer.fst"
                                                                (Prims.of_int (127))
                                                                (Prims.of_int (14))
                                                                (Prims.of_int (127))
                                                                (Prims.of_int (37)))
                                                             (FStar_Range.mk_range
                                                                "FStar.Printf.fst"
                                                                (Prims.of_int (121))
                                                                (Prims.of_int (8))
                                                                (Prims.of_int (123))
                                                                (Prims.of_int (44)))
                                                             (Obj.magic
                                                                (term_to_string
                                                                   inames))
                                                             (fun uu___3 ->
                                                                FStar_Tactics_Effect.lift_div_tac
                                                                  (fun uu___4
                                                                    ->
                                                                    fun x ->
                                                                    fun x1 ->
                                                                    fun x2 ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    "STAtomic "
                                                                    (Prims.strcat
                                                                    uu___3
                                                                    " "))
                                                                    (Prims.strcat
                                                                    x " "))
                                                                    (Prims.strcat
                                                                    x1 " "))
                                                                    (Prims.strcat
                                                                    x2 "")))))
                                                       (fun uu___3 ->
                                                          FStar_Tactics_Effect.lift_div_tac
                                                            (fun uu___4 ->
                                                               uu___3 uu___2))))
                                                 uu___2)))
                                      (fun uu___2 ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___3 -> uu___2 uu___1))))
                                uu___1)))
                     (fun uu___1 ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___2 -> uu___1 uu___)))) uu___)
    | Pulse_Syntax_Base.C_STGhost (inames, s) ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
             (Prims.of_int (137)) (Prims.of_int (14)) (Prims.of_int (137))
             (Prims.of_int (37)))
          (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
             (Prims.of_int (133)) (Prims.of_int (6)) (Prims.of_int (137))
             (Prims.of_int (37)))
          (Obj.magic (term_to_string s.Pulse_Syntax_Base.post))
          (fun uu___ ->
             (fun uu___ ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                        (Prims.of_int (133)) (Prims.of_int (6))
                        (Prims.of_int (137)) (Prims.of_int (37)))
                     (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                        (Prims.of_int (133)) (Prims.of_int (6))
                        (Prims.of_int (137)) (Prims.of_int (37)))
                     (Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                              (Prims.of_int (136)) (Prims.of_int (14))
                              (Prims.of_int (136)) (Prims.of_int (36)))
                           (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                              (Prims.of_int (133)) (Prims.of_int (6))
                              (Prims.of_int (137)) (Prims.of_int (37)))
                           (Obj.magic
                              (term_to_string s.Pulse_Syntax_Base.pre))
                           (fun uu___1 ->
                              (fun uu___1 ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Range.mk_range
                                         "Pulse.Syntax.Printer.fst"
                                         (Prims.of_int (133))
                                         (Prims.of_int (6))
                                         (Prims.of_int (137))
                                         (Prims.of_int (37)))
                                      (FStar_Range.mk_range
                                         "Pulse.Syntax.Printer.fst"
                                         (Prims.of_int (133))
                                         (Prims.of_int (6))
                                         (Prims.of_int (137))
                                         (Prims.of_int (37)))
                                      (Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Range.mk_range
                                               "Pulse.Syntax.Printer.fst"
                                               (Prims.of_int (135))
                                               (Prims.of_int (14))
                                               (Prims.of_int (135))
                                               (Prims.of_int (36)))
                                            (FStar_Range.mk_range
                                               "Pulse.Syntax.Printer.fst"
                                               (Prims.of_int (133))
                                               (Prims.of_int (6))
                                               (Prims.of_int (137))
                                               (Prims.of_int (37)))
                                            (Obj.magic
                                               (term_to_string
                                                  s.Pulse_Syntax_Base.res))
                                            (fun uu___2 ->
                                               (fun uu___2 ->
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Range.mk_range
                                                          "Pulse.Syntax.Printer.fst"
                                                          (Prims.of_int (133))
                                                          (Prims.of_int (6))
                                                          (Prims.of_int (137))
                                                          (Prims.of_int (37)))
                                                       (FStar_Range.mk_range
                                                          "Pulse.Syntax.Printer.fst"
                                                          (Prims.of_int (133))
                                                          (Prims.of_int (6))
                                                          (Prims.of_int (137))
                                                          (Prims.of_int (37)))
                                                       (Obj.magic
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (FStar_Range.mk_range
                                                                "Pulse.Syntax.Printer.fst"
                                                                (Prims.of_int (134))
                                                                (Prims.of_int (14))
                                                                (Prims.of_int (134))
                                                                (Prims.of_int (37)))
                                                             (FStar_Range.mk_range
                                                                "FStar.Printf.fst"
                                                                (Prims.of_int (121))
                                                                (Prims.of_int (8))
                                                                (Prims.of_int (123))
                                                                (Prims.of_int (44)))
                                                             (Obj.magic
                                                                (term_to_string
                                                                   inames))
                                                             (fun uu___3 ->
                                                                FStar_Tactics_Effect.lift_div_tac
                                                                  (fun uu___4
                                                                    ->
                                                                    fun x ->
                                                                    fun x1 ->
                                                                    fun x2 ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    "STGhost "
                                                                    (Prims.strcat
                                                                    uu___3
                                                                    " "))
                                                                    (Prims.strcat
                                                                    x " "))
                                                                    (Prims.strcat
                                                                    x1 " "))
                                                                    (Prims.strcat
                                                                    x2 "")))))
                                                       (fun uu___3 ->
                                                          FStar_Tactics_Effect.lift_div_tac
                                                            (fun uu___4 ->
                                                               uu___3 uu___2))))
                                                 uu___2)))
                                      (fun uu___2 ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___3 -> uu___2 uu___1))))
                                uu___1)))
                     (fun uu___1 ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___2 -> uu___1 uu___)))) uu___)
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
      FStar_Tactics_Effect.tac_bind
        (FStar_Range.mk_range "Pulse.Syntax.Printer.fst" (Prims.of_int (147))
           (Prims.of_int (22)) (Prims.of_int (147)) (Prims.of_int (46)))
        (FStar_Range.mk_range "Pulse.Syntax.Printer.fst" (Prims.of_int (147))
           (Prims.of_int (4)) (Prims.of_int (147)) (Prims.of_int (46)))
        (Obj.magic (FStar_Tactics_Util.map term_to_string t))
        (fun uu___ ->
           FStar_Tactics_Effect.lift_div_tac
             (fun uu___1 -> FStar_String.concat sep uu___))
let rec (st_term_to_string :
  Pulse_Syntax_Base.st_term ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    match t.Pulse_Syntax_Base.term1 with
    | Pulse_Syntax_Base.Tm_Return
        { Pulse_Syntax_Base.ctag = ctag;
          Pulse_Syntax_Base.insert_eq = insert_eq;
          Pulse_Syntax_Base.term = term;_}
        ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
             (Prims.of_int (159)) (Prims.of_int (8)) (Prims.of_int (159))
             (Prims.of_int (29)))
          (FStar_Range.mk_range "prims.fst" (Prims.of_int (590))
             (Prims.of_int (19)) (Prims.of_int (590)) (Prims.of_int (31)))
          (Obj.magic (term_to_string term))
          (fun uu___ ->
             FStar_Tactics_Effect.lift_div_tac
               (fun uu___1 ->
                  Prims.strcat
                    (Prims.strcat
                       (Prims.strcat "return_"
                          (Prims.strcat
                             (match ctag with
                              | Pulse_Syntax_Base.STT -> "stt"
                              | Pulse_Syntax_Base.STT_Atomic -> "stt_atomic"
                              | Pulse_Syntax_Base.STT_Ghost -> "stt_ghost")
                             ""))
                       (Prims.strcat (if insert_eq then "" else "_noeq") " "))
                    (Prims.strcat uu___ "")))
    | Pulse_Syntax_Base.Tm_STApp
        { Pulse_Syntax_Base.head = head;
          Pulse_Syntax_Base.arg_qual = arg_qual;
          Pulse_Syntax_Base.arg = arg;_}
        ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
             (Prims.of_int (166)) (Prims.of_int (8)) (Prims.of_int (166))
             (Prims.of_int (28)))
          (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
             (Prims.of_int (162)) (Prims.of_int (6)) (Prims.of_int (166))
             (Prims.of_int (28))) (Obj.magic (term_to_string arg))
          (fun uu___ ->
             (fun uu___ ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                        (Prims.of_int (162)) (Prims.of_int (6))
                        (Prims.of_int (166)) (Prims.of_int (28)))
                     (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                        (Prims.of_int (162)) (Prims.of_int (6))
                        (Prims.of_int (166)) (Prims.of_int (28)))
                     (Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                              (Prims.of_int (162)) (Prims.of_int (6))
                              (Prims.of_int (166)) (Prims.of_int (28)))
                           (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                              (Prims.of_int (162)) (Prims.of_int (6))
                              (Prims.of_int (166)) (Prims.of_int (28)))
                           (Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Range.mk_range
                                    "Pulse.Syntax.Printer.fst"
                                    (Prims.of_int (164)) (Prims.of_int (8))
                                    (Prims.of_int (164)) (Prims.of_int (29)))
                                 (FStar_Range.mk_range "FStar.Printf.fst"
                                    (Prims.of_int (121)) (Prims.of_int (8))
                                    (Prims.of_int (123)) (Prims.of_int (44)))
                                 (Obj.magic (term_to_string head))
                                 (fun uu___1 ->
                                    FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___2 ->
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
                                                     (Prims.strcat uu___1 " "))
                                                  (Prims.strcat x ""))
                                               (Prims.strcat x1 ")")))))
                           (fun uu___1 ->
                              FStar_Tactics_Effect.lift_div_tac
                                (fun uu___2 ->
                                   uu___1 (qual_to_string arg_qual)))))
                     (fun uu___1 ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___2 -> uu___1 uu___)))) uu___)
    | Pulse_Syntax_Base.Tm_Bind
        { Pulse_Syntax_Base.binder = binder; Pulse_Syntax_Base.head1 = head;
          Pulse_Syntax_Base.body1 = body;_}
        ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
             (Prims.of_int (172)) (Prims.of_int (8)) (Prims.of_int (172))
             (Prims.of_int (32)))
          (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
             (Prims.of_int (169)) (Prims.of_int (6)) (Prims.of_int (172))
             (Prims.of_int (32))) (Obj.magic (st_term_to_string body))
          (fun uu___ ->
             (fun uu___ ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                        (Prims.of_int (169)) (Prims.of_int (6))
                        (Prims.of_int (172)) (Prims.of_int (32)))
                     (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                        (Prims.of_int (169)) (Prims.of_int (6))
                        (Prims.of_int (172)) (Prims.of_int (32)))
                     (Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                              (Prims.of_int (171)) (Prims.of_int (8))
                              (Prims.of_int (171)) (Prims.of_int (32)))
                           (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                              (Prims.of_int (169)) (Prims.of_int (6))
                              (Prims.of_int (172)) (Prims.of_int (32)))
                           (Obj.magic (st_term_to_string head))
                           (fun uu___1 ->
                              (fun uu___1 ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Range.mk_range
                                         "Pulse.Syntax.Printer.fst"
                                         (Prims.of_int (169))
                                         (Prims.of_int (6))
                                         (Prims.of_int (172))
                                         (Prims.of_int (32)))
                                      (FStar_Range.mk_range
                                         "Pulse.Syntax.Printer.fst"
                                         (Prims.of_int (169))
                                         (Prims.of_int (6))
                                         (Prims.of_int (172))
                                         (Prims.of_int (32)))
                                      (Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Range.mk_range
                                               "Pulse.Syntax.Printer.fst"
                                               (Prims.of_int (170))
                                               (Prims.of_int (8))
                                               (Prims.of_int (170))
                                               (Prims.of_int (33)))
                                            (FStar_Range.mk_range
                                               "FStar.Printf.fst"
                                               (Prims.of_int (121))
                                               (Prims.of_int (8))
                                               (Prims.of_int (123))
                                               (Prims.of_int (44)))
                                            (Obj.magic
                                               (binder_to_string binder))
                                            (fun uu___2 ->
                                               FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___3 ->
                                                    fun x ->
                                                      fun x1 ->
                                                        Prims.strcat
                                                          (Prims.strcat
                                                             (Prims.strcat
                                                                "bind "
                                                                (Prims.strcat
                                                                   uu___2
                                                                   " = "))
                                                             (Prims.strcat x
                                                                " in "))
                                                          (Prims.strcat x1 "")))))
                                      (fun uu___2 ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___3 -> uu___2 uu___1))))
                                uu___1)))
                     (fun uu___1 ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___2 -> uu___1 uu___)))) uu___)
    | Pulse_Syntax_Base.Tm_TotBind
        { Pulse_Syntax_Base.head2 = head; Pulse_Syntax_Base.body2 = body;_}
        ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
             (Prims.of_int (177)) (Prims.of_int (8)) (Prims.of_int (177))
             (Prims.of_int (32)))
          (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
             (Prims.of_int (175)) (Prims.of_int (6)) (Prims.of_int (177))
             (Prims.of_int (32))) (Obj.magic (st_term_to_string body))
          (fun uu___ ->
             (fun uu___ ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                        (Prims.of_int (175)) (Prims.of_int (6))
                        (Prims.of_int (177)) (Prims.of_int (32)))
                     (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                        (Prims.of_int (175)) (Prims.of_int (6))
                        (Prims.of_int (177)) (Prims.of_int (32)))
                     (Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                              (Prims.of_int (176)) (Prims.of_int (8))
                              (Prims.of_int (176)) (Prims.of_int (29)))
                           (FStar_Range.mk_range "FStar.Printf.fst"
                              (Prims.of_int (121)) (Prims.of_int (8))
                              (Prims.of_int (123)) (Prims.of_int (44)))
                           (Obj.magic (term_to_string head))
                           (fun uu___1 ->
                              FStar_Tactics_Effect.lift_div_tac
                                (fun uu___2 ->
                                   fun x ->
                                     Prims.strcat
                                       (Prims.strcat "totbind _ = "
                                          (Prims.strcat uu___1 " in "))
                                       (Prims.strcat x "")))))
                     (fun uu___1 ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___2 -> uu___1 uu___)))) uu___)
    | Pulse_Syntax_Base.Tm_Abs
        { Pulse_Syntax_Base.b = b; Pulse_Syntax_Base.q = q;
          Pulse_Syntax_Base.pre1 = pre; Pulse_Syntax_Base.body = body;
          Pulse_Syntax_Base.ret_ty = uu___; Pulse_Syntax_Base.post1 = post;_}
        ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
             (Prims.of_int (185)) (Prims.of_int (14)) (Prims.of_int (185))
             (Prims.of_int (38)))
          (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
             (Prims.of_int (180)) (Prims.of_int (6)) (Prims.of_int (185))
             (Prims.of_int (38))) (Obj.magic (st_term_to_string body))
          (fun uu___1 ->
             (fun uu___1 ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                        (Prims.of_int (180)) (Prims.of_int (6))
                        (Prims.of_int (185)) (Prims.of_int (38)))
                     (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                        (Prims.of_int (180)) (Prims.of_int (6))
                        (Prims.of_int (185)) (Prims.of_int (38)))
                     (Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                              (Prims.of_int (184)) (Prims.of_int (14))
                              (Prims.of_int (184)) (Prims.of_int (39)))
                           (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                              (Prims.of_int (180)) (Prims.of_int (6))
                              (Prims.of_int (185)) (Prims.of_int (38)))
                           (Obj.magic (term_opt_to_string post))
                           (fun uu___2 ->
                              (fun uu___2 ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Range.mk_range
                                         "Pulse.Syntax.Printer.fst"
                                         (Prims.of_int (180))
                                         (Prims.of_int (6))
                                         (Prims.of_int (185))
                                         (Prims.of_int (38)))
                                      (FStar_Range.mk_range
                                         "Pulse.Syntax.Printer.fst"
                                         (Prims.of_int (180))
                                         (Prims.of_int (6))
                                         (Prims.of_int (185))
                                         (Prims.of_int (38)))
                                      (Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Range.mk_range
                                               "Pulse.Syntax.Printer.fst"
                                               (Prims.of_int (183))
                                               (Prims.of_int (14))
                                               (Prims.of_int (183))
                                               (Prims.of_int (38)))
                                            (FStar_Range.mk_range
                                               "Pulse.Syntax.Printer.fst"
                                               (Prims.of_int (180))
                                               (Prims.of_int (6))
                                               (Prims.of_int (185))
                                               (Prims.of_int (38)))
                                            (Obj.magic
                                               (term_opt_to_string pre))
                                            (fun uu___3 ->
                                               (fun uu___3 ->
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Range.mk_range
                                                          "Pulse.Syntax.Printer.fst"
                                                          (Prims.of_int (180))
                                                          (Prims.of_int (6))
                                                          (Prims.of_int (185))
                                                          (Prims.of_int (38)))
                                                       (FStar_Range.mk_range
                                                          "Pulse.Syntax.Printer.fst"
                                                          (Prims.of_int (180))
                                                          (Prims.of_int (6))
                                                          (Prims.of_int (185))
                                                          (Prims.of_int (38)))
                                                       (Obj.magic
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (FStar_Range.mk_range
                                                                "Pulse.Syntax.Printer.fst"
                                                                (Prims.of_int (182))
                                                                (Prims.of_int (14))
                                                                (Prims.of_int (182))
                                                                (Prims.of_int (34)))
                                                             (FStar_Range.mk_range
                                                                "FStar.Printf.fst"
                                                                (Prims.of_int (121))
                                                                (Prims.of_int (8))
                                                                (Prims.of_int (123))
                                                                (Prims.of_int (44)))
                                                             (Obj.magic
                                                                (binder_to_string
                                                                   b))
                                                             (fun uu___4 ->
                                                                FStar_Tactics_Effect.lift_div_tac
                                                                  (fun uu___5
                                                                    ->
                                                                    fun x ->
                                                                    fun x1 ->
                                                                    fun x2 ->
                                                                    Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    (Prims.strcat
                                                                    "(fun ("
                                                                    (Prims.strcat
                                                                    (qual_to_string
                                                                    q) ""))
                                                                    (Prims.strcat
                                                                    uu___4
                                                                    ") {"))
                                                                    (Prims.strcat
                                                                    x "} {_."))
                                                                    (Prims.strcat
                                                                    x1
                                                                    "} -> "))
                                                                    (Prims.strcat
                                                                    x2 ")")))))
                                                       (fun uu___4 ->
                                                          FStar_Tactics_Effect.lift_div_tac
                                                            (fun uu___5 ->
                                                               uu___4 uu___3))))
                                                 uu___3)))
                                      (fun uu___3 ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___4 -> uu___3 uu___2))))
                                uu___2)))
                     (fun uu___2 ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___3 -> uu___2 uu___1)))) uu___1)
    | Pulse_Syntax_Base.Tm_If
        { Pulse_Syntax_Base.b1 = b; Pulse_Syntax_Base.then_ = then_;
          Pulse_Syntax_Base.else_ = else_; Pulse_Syntax_Base.post2 = uu___;_}
        ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
             (Prims.of_int (191)) (Prims.of_int (8)) (Prims.of_int (191))
             (Prims.of_int (33)))
          (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
             (Prims.of_int (188)) (Prims.of_int (6)) (Prims.of_int (191))
             (Prims.of_int (33))) (Obj.magic (st_term_to_string else_))
          (fun uu___1 ->
             (fun uu___1 ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                        (Prims.of_int (188)) (Prims.of_int (6))
                        (Prims.of_int (191)) (Prims.of_int (33)))
                     (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                        (Prims.of_int (188)) (Prims.of_int (6))
                        (Prims.of_int (191)) (Prims.of_int (33)))
                     (Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                              (Prims.of_int (190)) (Prims.of_int (8))
                              (Prims.of_int (190)) (Prims.of_int (33)))
                           (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                              (Prims.of_int (188)) (Prims.of_int (6))
                              (Prims.of_int (191)) (Prims.of_int (33)))
                           (Obj.magic (st_term_to_string then_))
                           (fun uu___2 ->
                              (fun uu___2 ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Range.mk_range
                                         "Pulse.Syntax.Printer.fst"
                                         (Prims.of_int (188))
                                         (Prims.of_int (6))
                                         (Prims.of_int (191))
                                         (Prims.of_int (33)))
                                      (FStar_Range.mk_range
                                         "Pulse.Syntax.Printer.fst"
                                         (Prims.of_int (188))
                                         (Prims.of_int (6))
                                         (Prims.of_int (191))
                                         (Prims.of_int (33)))
                                      (Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Range.mk_range
                                               "Pulse.Syntax.Printer.fst"
                                               (Prims.of_int (189))
                                               (Prims.of_int (8))
                                               (Prims.of_int (189))
                                               (Prims.of_int (26)))
                                            (FStar_Range.mk_range
                                               "FStar.Printf.fst"
                                               (Prims.of_int (121))
                                               (Prims.of_int (8))
                                               (Prims.of_int (123))
                                               (Prims.of_int (44)))
                                            (Obj.magic (term_to_string b))
                                            (fun uu___3 ->
                                               FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___4 ->
                                                    fun x ->
                                                      fun x1 ->
                                                        Prims.strcat
                                                          (Prims.strcat
                                                             (Prims.strcat
                                                                "(if "
                                                                (Prims.strcat
                                                                   uu___3
                                                                   " then "))
                                                             (Prims.strcat x
                                                                " else "))
                                                          (Prims.strcat x1
                                                             ")")))))
                                      (fun uu___3 ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___4 -> uu___3 uu___2))))
                                uu___2)))
                     (fun uu___2 ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___3 -> uu___2 uu___1)))) uu___1)
    | Pulse_Syntax_Base.Tm_ElimExists { Pulse_Syntax_Base.p = p;_} ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
             (Prims.of_int (195)) (Prims.of_int (8)) (Prims.of_int (195))
             (Prims.of_int (26)))
          (FStar_Range.mk_range "prims.fst" (Prims.of_int (590))
             (Prims.of_int (19)) (Prims.of_int (590)) (Prims.of_int (31)))
          (Obj.magic (term_to_string p))
          (fun uu___ ->
             FStar_Tactics_Effect.lift_div_tac
               (fun uu___1 ->
                  Prims.strcat "elim_exists " (Prims.strcat uu___ "")))
    | Pulse_Syntax_Base.Tm_IntroExists
        { Pulse_Syntax_Base.erased = false; Pulse_Syntax_Base.p1 = p;
          Pulse_Syntax_Base.witnesses = witnesses;_}
        ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
             (Prims.of_int (200)) (Prims.of_int (8)) (Prims.of_int (200))
             (Prims.of_int (43)))
          (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
             (Prims.of_int (198)) (Prims.of_int (6)) (Prims.of_int (200))
             (Prims.of_int (43)))
          (Obj.magic (term_list_to_string " " witnesses))
          (fun uu___ ->
             (fun uu___ ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                        (Prims.of_int (198)) (Prims.of_int (6))
                        (Prims.of_int (200)) (Prims.of_int (43)))
                     (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                        (Prims.of_int (198)) (Prims.of_int (6))
                        (Prims.of_int (200)) (Prims.of_int (43)))
                     (Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                              (Prims.of_int (199)) (Prims.of_int (8))
                              (Prims.of_int (199)) (Prims.of_int (26)))
                           (FStar_Range.mk_range "FStar.Printf.fst"
                              (Prims.of_int (121)) (Prims.of_int (8))
                              (Prims.of_int (123)) (Prims.of_int (44)))
                           (Obj.magic (term_to_string p))
                           (fun uu___1 ->
                              FStar_Tactics_Effect.lift_div_tac
                                (fun uu___2 ->
                                   fun x ->
                                     Prims.strcat
                                       (Prims.strcat "intro_exists "
                                          (Prims.strcat uu___1 " "))
                                       (Prims.strcat x "")))))
                     (fun uu___1 ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___2 -> uu___1 uu___)))) uu___)
    | Pulse_Syntax_Base.Tm_IntroExists
        { Pulse_Syntax_Base.erased = true; Pulse_Syntax_Base.p1 = p;
          Pulse_Syntax_Base.witnesses = witnesses;_}
        ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
             (Prims.of_int (205)) (Prims.of_int (8)) (Prims.of_int (205))
             (Prims.of_int (43)))
          (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
             (Prims.of_int (203)) (Prims.of_int (6)) (Prims.of_int (205))
             (Prims.of_int (43)))
          (Obj.magic (term_list_to_string " " witnesses))
          (fun uu___ ->
             (fun uu___ ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                        (Prims.of_int (203)) (Prims.of_int (6))
                        (Prims.of_int (205)) (Prims.of_int (43)))
                     (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                        (Prims.of_int (203)) (Prims.of_int (6))
                        (Prims.of_int (205)) (Prims.of_int (43)))
                     (Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                              (Prims.of_int (204)) (Prims.of_int (8))
                              (Prims.of_int (204)) (Prims.of_int (26)))
                           (FStar_Range.mk_range "FStar.Printf.fst"
                              (Prims.of_int (121)) (Prims.of_int (8))
                              (Prims.of_int (123)) (Prims.of_int (44)))
                           (Obj.magic (term_to_string p))
                           (fun uu___1 ->
                              FStar_Tactics_Effect.lift_div_tac
                                (fun uu___2 ->
                                   fun x ->
                                     Prims.strcat
                                       (Prims.strcat "intro_exists_erased "
                                          (Prims.strcat uu___1 " "))
                                       (Prims.strcat x "")))))
                     (fun uu___1 ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___2 -> uu___1 uu___)))) uu___)
    | Pulse_Syntax_Base.Tm_While
        { Pulse_Syntax_Base.invariant = invariant;
          Pulse_Syntax_Base.condition = condition;
          Pulse_Syntax_Base.body3 = body;_}
        ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
             (Prims.of_int (211)) (Prims.of_int (8)) (Prims.of_int (211))
             (Prims.of_int (32)))
          (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
             (Prims.of_int (208)) (Prims.of_int (6)) (Prims.of_int (211))
             (Prims.of_int (32))) (Obj.magic (st_term_to_string body))
          (fun uu___ ->
             (fun uu___ ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                        (Prims.of_int (208)) (Prims.of_int (6))
                        (Prims.of_int (211)) (Prims.of_int (32)))
                     (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                        (Prims.of_int (208)) (Prims.of_int (6))
                        (Prims.of_int (211)) (Prims.of_int (32)))
                     (Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                              (Prims.of_int (210)) (Prims.of_int (8))
                              (Prims.of_int (210)) (Prims.of_int (37)))
                           (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                              (Prims.of_int (208)) (Prims.of_int (6))
                              (Prims.of_int (211)) (Prims.of_int (32)))
                           (Obj.magic (st_term_to_string condition))
                           (fun uu___1 ->
                              (fun uu___1 ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Range.mk_range
                                         "Pulse.Syntax.Printer.fst"
                                         (Prims.of_int (208))
                                         (Prims.of_int (6))
                                         (Prims.of_int (211))
                                         (Prims.of_int (32)))
                                      (FStar_Range.mk_range
                                         "Pulse.Syntax.Printer.fst"
                                         (Prims.of_int (208))
                                         (Prims.of_int (6))
                                         (Prims.of_int (211))
                                         (Prims.of_int (32)))
                                      (Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Range.mk_range
                                               "Pulse.Syntax.Printer.fst"
                                               (Prims.of_int (209))
                                               (Prims.of_int (8))
                                               (Prims.of_int (209))
                                               (Prims.of_int (34)))
                                            (FStar_Range.mk_range
                                               "FStar.Printf.fst"
                                               (Prims.of_int (121))
                                               (Prims.of_int (8))
                                               (Prims.of_int (123))
                                               (Prims.of_int (44)))
                                            (Obj.magic
                                               (term_to_string invariant))
                                            (fun uu___2 ->
                                               FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___3 ->
                                                    fun x ->
                                                      fun x1 ->
                                                        Prims.strcat
                                                          (Prims.strcat
                                                             (Prims.strcat
                                                                "while<"
                                                                (Prims.strcat
                                                                   uu___2
                                                                   "> ("))
                                                             (Prims.strcat x
                                                                ") {"))
                                                          (Prims.strcat x1
                                                             "}")))))
                                      (fun uu___2 ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___3 -> uu___2 uu___1))))
                                uu___1)))
                     (fun uu___1 ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___2 -> uu___1 uu___)))) uu___)
    | Pulse_Syntax_Base.Tm_Par
        { Pulse_Syntax_Base.pre11 = pre1; Pulse_Syntax_Base.body11 = body1;
          Pulse_Syntax_Base.post11 = post1; Pulse_Syntax_Base.pre2 = pre2;
          Pulse_Syntax_Base.body21 = body2;
          Pulse_Syntax_Base.post21 = post2;_}
        ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
             (Prims.of_int (220)) (Prims.of_int (8)) (Prims.of_int (220))
             (Prims.of_int (30)))
          (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
             (Prims.of_int (214)) (Prims.of_int (6)) (Prims.of_int (220))
             (Prims.of_int (30))) (Obj.magic (term_to_string post2))
          (fun uu___ ->
             (fun uu___ ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                        (Prims.of_int (214)) (Prims.of_int (6))
                        (Prims.of_int (220)) (Prims.of_int (30)))
                     (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                        (Prims.of_int (214)) (Prims.of_int (6))
                        (Prims.of_int (220)) (Prims.of_int (30)))
                     (Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                              (Prims.of_int (219)) (Prims.of_int (8))
                              (Prims.of_int (219)) (Prims.of_int (33)))
                           (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                              (Prims.of_int (214)) (Prims.of_int (6))
                              (Prims.of_int (220)) (Prims.of_int (30)))
                           (Obj.magic (st_term_to_string body2))
                           (fun uu___1 ->
                              (fun uu___1 ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Range.mk_range
                                         "Pulse.Syntax.Printer.fst"
                                         (Prims.of_int (214))
                                         (Prims.of_int (6))
                                         (Prims.of_int (220))
                                         (Prims.of_int (30)))
                                      (FStar_Range.mk_range
                                         "Pulse.Syntax.Printer.fst"
                                         (Prims.of_int (214))
                                         (Prims.of_int (6))
                                         (Prims.of_int (220))
                                         (Prims.of_int (30)))
                                      (Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Range.mk_range
                                               "Pulse.Syntax.Printer.fst"
                                               (Prims.of_int (218))
                                               (Prims.of_int (8))
                                               (Prims.of_int (218))
                                               (Prims.of_int (29)))
                                            (FStar_Range.mk_range
                                               "Pulse.Syntax.Printer.fst"
                                               (Prims.of_int (214))
                                               (Prims.of_int (6))
                                               (Prims.of_int (220))
                                               (Prims.of_int (30)))
                                            (Obj.magic (term_to_string pre2))
                                            (fun uu___2 ->
                                               (fun uu___2 ->
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Range.mk_range
                                                          "Pulse.Syntax.Printer.fst"
                                                          (Prims.of_int (214))
                                                          (Prims.of_int (6))
                                                          (Prims.of_int (220))
                                                          (Prims.of_int (30)))
                                                       (FStar_Range.mk_range
                                                          "Pulse.Syntax.Printer.fst"
                                                          (Prims.of_int (214))
                                                          (Prims.of_int (6))
                                                          (Prims.of_int (220))
                                                          (Prims.of_int (30)))
                                                       (Obj.magic
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (FStar_Range.mk_range
                                                                "Pulse.Syntax.Printer.fst"
                                                                (Prims.of_int (217))
                                                                (Prims.of_int (8))
                                                                (Prims.of_int (217))
                                                                (Prims.of_int (30)))
                                                             (FStar_Range.mk_range
                                                                "Pulse.Syntax.Printer.fst"
                                                                (Prims.of_int (214))
                                                                (Prims.of_int (6))
                                                                (Prims.of_int (220))
                                                                (Prims.of_int (30)))
                                                             (Obj.magic
                                                                (term_to_string
                                                                   post1))
                                                             (fun uu___3 ->
                                                                (fun uu___3
                                                                   ->
                                                                   Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (214))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (220))
                                                                    (Prims.of_int (30)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (214))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (220))
                                                                    (Prims.of_int (30)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (216))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (216))
                                                                    (Prims.of_int (33)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (214))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (220))
                                                                    (Prims.of_int (30)))
                                                                    (Obj.magic
                                                                    (st_term_to_string
                                                                    body1))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (214))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (220))
                                                                    (Prims.of_int (30)))
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (214))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (220))
                                                                    (Prims.of_int (30)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "Pulse.Syntax.Printer.fst"
                                                                    (Prims.of_int (215))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (215))
                                                                    (Prims.of_int (29)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Printf.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (44)))
                                                                    (Obj.magic
                                                                    (term_to_string
                                                                    pre1))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
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
                                                                    uu___5
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
                                                                    x4 ")")))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    uu___5
                                                                    uu___4))))
                                                                    uu___4)))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    uu___4
                                                                    uu___3))))
                                                                  uu___3)))
                                                       (fun uu___3 ->
                                                          FStar_Tactics_Effect.lift_div_tac
                                                            (fun uu___4 ->
                                                               uu___3 uu___2))))
                                                 uu___2)))
                                      (fun uu___2 ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___3 -> uu___2 uu___1))))
                                uu___1)))
                     (fun uu___1 ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___2 -> uu___1 uu___)))) uu___)
    | Pulse_Syntax_Base.Tm_Rewrite
        { Pulse_Syntax_Base.t1 = t1; Pulse_Syntax_Base.t2 = t2;_} ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
             (Prims.of_int (225)) (Prims.of_int (14)) (Prims.of_int (225))
             (Prims.of_int (33)))
          (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
             (Prims.of_int (223)) (Prims.of_int (6)) (Prims.of_int (225))
             (Prims.of_int (33))) (Obj.magic (term_to_string t2))
          (fun uu___ ->
             (fun uu___ ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                        (Prims.of_int (223)) (Prims.of_int (6))
                        (Prims.of_int (225)) (Prims.of_int (33)))
                     (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                        (Prims.of_int (223)) (Prims.of_int (6))
                        (Prims.of_int (225)) (Prims.of_int (33)))
                     (Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                              (Prims.of_int (224)) (Prims.of_int (8))
                              (Prims.of_int (224)) (Prims.of_int (27)))
                           (FStar_Range.mk_range "FStar.Printf.fst"
                              (Prims.of_int (121)) (Prims.of_int (8))
                              (Prims.of_int (123)) (Prims.of_int (44)))
                           (Obj.magic (term_to_string t1))
                           (fun uu___1 ->
                              FStar_Tactics_Effect.lift_div_tac
                                (fun uu___2 ->
                                   fun x ->
                                     Prims.strcat
                                       (Prims.strcat "rewrite "
                                          (Prims.strcat uu___1 " "))
                                       (Prims.strcat x "")))))
                     (fun uu___1 ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___2 -> uu___1 uu___)))) uu___)
    | Pulse_Syntax_Base.Tm_WithLocal
        { Pulse_Syntax_Base.initializer1 = initializer1;
          Pulse_Syntax_Base.body4 = body;_}
        ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
             (Prims.of_int (230)) (Prims.of_int (8)) (Prims.of_int (230))
             (Prims.of_int (32)))
          (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
             (Prims.of_int (228)) (Prims.of_int (6)) (Prims.of_int (230))
             (Prims.of_int (32))) (Obj.magic (st_term_to_string body))
          (fun uu___ ->
             (fun uu___ ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                        (Prims.of_int (228)) (Prims.of_int (6))
                        (Prims.of_int (230)) (Prims.of_int (32)))
                     (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                        (Prims.of_int (228)) (Prims.of_int (6))
                        (Prims.of_int (230)) (Prims.of_int (32)))
                     (Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                              (Prims.of_int (229)) (Prims.of_int (8))
                              (Prims.of_int (229)) (Prims.of_int (36)))
                           (FStar_Range.mk_range "FStar.Printf.fst"
                              (Prims.of_int (121)) (Prims.of_int (8))
                              (Prims.of_int (123)) (Prims.of_int (44)))
                           (Obj.magic (term_to_string initializer1))
                           (fun uu___1 ->
                              FStar_Tactics_Effect.lift_div_tac
                                (fun uu___2 ->
                                   fun x ->
                                     Prims.strcat
                                       (Prims.strcat "let mut _ = "
                                          (Prims.strcat uu___1 " in "))
                                       (Prims.strcat x "")))))
                     (fun uu___1 ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___2 -> uu___1 uu___)))) uu___)
    | Pulse_Syntax_Base.Tm_Admit
        { Pulse_Syntax_Base.ctag1 = ctag; Pulse_Syntax_Base.u1 = u;
          Pulse_Syntax_Base.typ = typ; Pulse_Syntax_Base.post3 = post;_}
        ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
             (Prims.of_int (240)) (Prims.of_int (8)) (Prims.of_int (242))
             (Prims.of_int (60)))
          (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
             (Prims.of_int (233)) (Prims.of_int (6)) (Prims.of_int (242))
             (Prims.of_int (60)))
          (match post with
           | FStar_Pervasives_Native.None ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> "")))
           | FStar_Pervasives_Native.Some post1 ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                          (Prims.of_int (242)) (Prims.of_int (38))
                          (Prims.of_int (242)) (Prims.of_int (59)))
                       (FStar_Range.mk_range "prims.fst" (Prims.of_int (590))
                          (Prims.of_int (19)) (Prims.of_int (590))
                          (Prims.of_int (31)))
                       (Obj.magic (term_to_string post1))
                       (fun uu___ ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___1 ->
                               Prims.strcat " " (Prims.strcat uu___ ""))))))
          (fun uu___ ->
             (fun uu___ ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                        (Prims.of_int (233)) (Prims.of_int (6))
                        (Prims.of_int (242)) (Prims.of_int (60)))
                     (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                        (Prims.of_int (233)) (Prims.of_int (6))
                        (Prims.of_int (242)) (Prims.of_int (60)))
                     (Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Range.mk_range "Pulse.Syntax.Printer.fst"
                              (Prims.of_int (239)) (Prims.of_int (8))
                              (Prims.of_int (239)) (Prims.of_int (28)))
                           (FStar_Range.mk_range "FStar.Printf.fst"
                              (Prims.of_int (121)) (Prims.of_int (8))
                              (Prims.of_int (123)) (Prims.of_int (44)))
                           (Obj.magic (term_to_string typ))
                           (fun uu___1 ->
                              FStar_Tactics_Effect.lift_div_tac
                                (fun uu___2 ->
                                   fun x ->
                                     Prims.strcat
                                       (Prims.strcat
                                          (Prims.strcat
                                             (Prims.strcat ""
                                                (Prims.strcat
                                                   (match ctag with
                                                    | Pulse_Syntax_Base.STT
                                                        -> "stt_admit"
                                                    | Pulse_Syntax_Base.STT_Atomic
                                                        -> "stt_atomic_admit"
                                                    | Pulse_Syntax_Base.STT_Ghost
                                                        -> "stt_ghost_admit")
                                                   "<"))
                                             (Prims.strcat
                                                (universe_to_string
                                                   Prims.int_zero u) "> "))
                                          (Prims.strcat uu___1 ""))
                                       (Prims.strcat x "")))))
                     (fun uu___1 ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___2 -> uu___1 uu___)))) uu___)
    | Pulse_Syntax_Base.Tm_Protect { Pulse_Syntax_Base.t = t1;_} ->
        st_term_to_string t1