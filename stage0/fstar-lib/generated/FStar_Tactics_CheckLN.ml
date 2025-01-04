open Prims
let rec for_all :
  'a .
    ('a -> (Prims.bool, unit) FStar_Tactics_Effect.tac_repr) ->
      'a Prims.list -> (Prims.bool, unit) FStar_Tactics_Effect.tac_repr
  =
  fun uu___1 ->
    fun uu___ ->
      (fun p ->
         fun l ->
           match l with
           | [] ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> true)))
           | x::xs ->
               Obj.magic
                 (Obj.repr
                    (let uu___ = p x in
                     FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.CheckLN.fst"
                                (Prims.of_int (9)) (Prims.of_int (16))
                                (Prims.of_int (9)) (Prims.of_int (19)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.CheckLN.fst"
                                (Prims.of_int (9)) (Prims.of_int (13))
                                (Prims.of_int (9)) (Prims.of_int (48)))))
                       (Obj.magic uu___)
                       (fun uu___1 ->
                          (fun uu___1 ->
                             if uu___1
                             then Obj.magic (Obj.repr (for_all p xs))
                             else
                               Obj.magic
                                 (Obj.repr
                                    (FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___3 -> false)))) uu___1))))
        uu___1 uu___
let rec (check :
  FStar_Tactics_NamedView.term ->
    (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    let uu___ = FStar_Tactics_NamedView.inspect t in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.CheckLN.fst"
               (Prims.of_int (12)) (Prims.of_int (8)) (Prims.of_int (12))
               (Prims.of_int (17)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.CheckLN.fst"
               (Prims.of_int (12)) (Prims.of_int (2)) (Prims.of_int (41))
               (Prims.of_int (21))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun uu___1 ->
            match uu___1 with
            | FStar_Tactics_NamedView.Tv_BVar bv ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> false)))
            | FStar_Tactics_NamedView.Tv_Const uu___2 ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac (fun uu___3 -> true)))
            | FStar_Tactics_NamedView.Tv_Uvar (uu___2, uu___3) ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac (fun uu___4 -> false)))
            | FStar_Tactics_NamedView.Tv_Var uu___2 ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac (fun uu___3 -> true)))
            | FStar_Tactics_NamedView.Tv_FVar uu___2 ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac (fun uu___3 -> true)))
            | FStar_Tactics_NamedView.Tv_UInst (uu___2, us) ->
                Obj.magic (Obj.repr (for_all check_u us))
            | FStar_Tactics_NamedView.Tv_App (hd, (a, q)) ->
                Obj.magic
                  (Obj.repr
                     (let uu___2 = check hd in
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.CheckLN.fst"
                                 (Prims.of_int (24)) (Prims.of_int (27))
                                 (Prims.of_int (24)) (Prims.of_int (35)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.CheckLN.fst"
                                 (Prims.of_int (24)) (Prims.of_int (24))
                                 (Prims.of_int (24)) (Prims.of_int (59)))))
                        (Obj.magic uu___2)
                        (fun uu___3 ->
                           (fun uu___3 ->
                              if uu___3
                              then Obj.magic (Obj.repr (check a))
                              else
                                Obj.magic
                                  (Obj.repr
                                     (FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___5 -> false)))) uu___3)))
            | FStar_Tactics_NamedView.Tv_Abs (b, body) ->
                Obj.magic
                  (Obj.repr
                     (let uu___2 = check b.FStar_Tactics_NamedView.sort in
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.CheckLN.fst"
                                 (Prims.of_int (25)) (Prims.of_int (24))
                                 (Prims.of_int (25)) (Prims.of_int (36)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.CheckLN.fst"
                                 (Prims.of_int (25)) (Prims.of_int (21))
                                 (Prims.of_int (25)) (Prims.of_int (63)))))
                        (Obj.magic uu___2)
                        (fun uu___3 ->
                           (fun uu___3 ->
                              if uu___3
                              then Obj.magic (Obj.repr (check body))
                              else
                                Obj.magic
                                  (Obj.repr
                                     (FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___5 -> false)))) uu___3)))
            | FStar_Tactics_NamedView.Tv_Arrow (b, c) ->
                Obj.magic
                  (Obj.repr
                     (let uu___2 = check b.FStar_Tactics_NamedView.sort in
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.CheckLN.fst"
                                 (Prims.of_int (26)) (Prims.of_int (23))
                                 (Prims.of_int (26)) (Prims.of_int (35)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.CheckLN.fst"
                                 (Prims.of_int (26)) (Prims.of_int (20))
                                 (Prims.of_int (26)) (Prims.of_int (64)))))
                        (Obj.magic uu___2)
                        (fun uu___3 ->
                           (fun uu___3 ->
                              if uu___3
                              then Obj.magic (Obj.repr (check_comp c))
                              else
                                Obj.magic
                                  (Obj.repr
                                     (FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___5 -> false)))) uu___3)))
            | FStar_Tactics_NamedView.Tv_Type u ->
                Obj.magic (Obj.repr (check_u u))
            | FStar_Tactics_NamedView.Tv_Refine (b, ref) ->
                Obj.magic
                  (Obj.repr
                     (let uu___2 = check b.FStar_Tactics_NamedView.sort in
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.CheckLN.fst"
                                 (Prims.of_int (28)) (Prims.of_int (26))
                                 (Prims.of_int (28)) (Prims.of_int (38)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.CheckLN.fst"
                                 (Prims.of_int (28)) (Prims.of_int (23))
                                 (Prims.of_int (28)) (Prims.of_int (64)))))
                        (Obj.magic uu___2)
                        (fun uu___3 ->
                           (fun uu___3 ->
                              if uu___3
                              then Obj.magic (Obj.repr (check ref))
                              else
                                Obj.magic
                                  (Obj.repr
                                     (FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___5 -> false)))) uu___3)))
            | FStar_Tactics_NamedView.Tv_Let (recf, attrs, b, def, body) ->
                Obj.magic
                  (Obj.repr
                     (let uu___2 =
                        let uu___3 = for_all check attrs in
                        FStar_Tactics_Effect.tac_bind
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "FStar.Tactics.CheckLN.fst"
                                   (Prims.of_int (30)) (Prims.of_int (11))
                                   (Prims.of_int (30)) (Prims.of_int (32)))))
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "FStar.Tactics.CheckLN.fst"
                                   (Prims.of_int (30)) (Prims.of_int (7))
                                   (Prims.of_int (30)) (Prims.of_int (32)))))
                          (Obj.magic uu___3)
                          (fun uu___4 ->
                             FStar_Tactics_Effect.lift_div_tac
                               (fun uu___5 -> Prims.op_Negation uu___4)) in
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.CheckLN.fst"
                                 (Prims.of_int (30)) (Prims.of_int (7))
                                 (Prims.of_int (30)) (Prims.of_int (32)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.CheckLN.fst"
                                 (Prims.of_int (30)) (Prims.of_int (4))
                                 (Prims.of_int (32)) (Prims.of_int (14)))))
                        (Obj.magic uu___2)
                        (fun uu___3 ->
                           (fun uu___3 ->
                              if uu___3
                              then
                                Obj.magic
                                  (Obj.repr
                                     (FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___4 -> false)))
                              else
                                Obj.magic
                                  (Obj.repr
                                     (let uu___5 =
                                        let uu___6 = check def in
                                        FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "FStar.Tactics.CheckLN.fst"
                                                   (Prims.of_int (31))
                                                   (Prims.of_int (11))
                                                   (Prims.of_int (31))
                                                   (Prims.of_int (22)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "FStar.Tactics.CheckLN.fst"
                                                   (Prims.of_int (31))
                                                   (Prims.of_int (7))
                                                   (Prims.of_int (31))
                                                   (Prims.of_int (22)))))
                                          (Obj.magic uu___6)
                                          (fun uu___7 ->
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___8 ->
                                                  Prims.op_Negation uu___7)) in
                                      FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "FStar.Tactics.CheckLN.fst"
                                                 (Prims.of_int (31))
                                                 (Prims.of_int (7))
                                                 (Prims.of_int (31))
                                                 (Prims.of_int (22)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "FStar.Tactics.CheckLN.fst"
                                                 (Prims.of_int (31))
                                                 (Prims.of_int (4))
                                                 (Prims.of_int (32))
                                                 (Prims.of_int (14)))))
                                        (Obj.magic uu___5)
                                        (fun uu___6 ->
                                           (fun uu___6 ->
                                              if uu___6
                                              then
                                                Obj.magic
                                                  (Obj.repr
                                                     (FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___7 -> false)))
                                              else
                                                Obj.magic
                                                  (Obj.repr (check body)))
                                             uu___6)))) uu___3)))
            | FStar_Tactics_NamedView.Tv_Match (sc, uu___2, brs) ->
                Obj.magic
                  (Obj.repr
                     (let uu___3 = check sc in
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.CheckLN.fst"
                                 (Prims.of_int (34)) (Prims.of_int (7))
                                 (Prims.of_int (34)) (Prims.of_int (15)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.CheckLN.fst"
                                 (Prims.of_int (34)) (Prims.of_int (4))
                                 (Prims.of_int (34)) (Prims.of_int (52)))))
                        (Obj.magic uu___3)
                        (fun uu___4 ->
                           (fun uu___4 ->
                              if uu___4
                              then
                                Obj.magic (Obj.repr (for_all check_br brs))
                              else
                                Obj.magic
                                  (Obj.repr
                                     (FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___6 -> false)))) uu___4)))
            | FStar_Tactics_NamedView.Tv_AscribedT (e, t1, uu___2, uu___3) ->
                Obj.magic
                  (Obj.repr
                     (let uu___4 = check e in
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.CheckLN.fst"
                                 (Prims.of_int (36)) (Prims.of_int (7))
                                 (Prims.of_int (36)) (Prims.of_int (14)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.CheckLN.fst"
                                 (Prims.of_int (36)) (Prims.of_int (4))
                                 (Prims.of_int (36)) (Prims.of_int (38)))))
                        (Obj.magic uu___4)
                        (fun uu___5 ->
                           (fun uu___5 ->
                              if uu___5
                              then Obj.magic (Obj.repr (check t1))
                              else
                                Obj.magic
                                  (Obj.repr
                                     (FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___7 -> false)))) uu___5)))
            | FStar_Tactics_NamedView.Tv_AscribedC (e, c, uu___2, uu___3) ->
                Obj.magic
                  (Obj.repr
                     (let uu___4 = check e in
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.CheckLN.fst"
                                 (Prims.of_int (38)) (Prims.of_int (7))
                                 (Prims.of_int (38)) (Prims.of_int (14)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.CheckLN.fst"
                                 (Prims.of_int (38)) (Prims.of_int (4))
                                 (Prims.of_int (38)) (Prims.of_int (43)))))
                        (Obj.magic uu___4)
                        (fun uu___5 ->
                           (fun uu___5 ->
                              if uu___5
                              then Obj.magic (Obj.repr (check_comp c))
                              else
                                Obj.magic
                                  (Obj.repr
                                     (FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___7 -> false)))) uu___5)))
            | FStar_Tactics_NamedView.Tv_Unknown ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> true)))
            | FStar_Tactics_NamedView.Tv_Unsupp ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> true))))
           uu___1)
and (check_u :
  FStar_Tactics_NamedView.universe ->
    (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    (fun u ->
       match FStar_Tactics_NamedView.inspect_universe u with
       | FStar_Tactics_NamedView.Uv_BVar uu___ ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> false)))
       | FStar_Tactics_NamedView.Uv_Name uu___ ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> true)))
       | FStar_Tactics_NamedView.Uv_Unif uu___ ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> false)))
       | FStar_Tactics_NamedView.Uv_Zero ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> true)))
       | FStar_Tactics_NamedView.Uv_Succ u1 ->
           Obj.magic (Obj.repr (check_u u1))
       | FStar_Tactics_NamedView.Uv_Max us ->
           Obj.magic (Obj.repr (for_all check_u us))
       | FStar_Tactics_NamedView.Uv_Unk ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> true))))
      uu___
and (check_comp :
  FStar_Tactics_NamedView.comp ->
    (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun c ->
    match c with
    | FStarC_Reflection_V2_Data.C_Total typ -> check typ
    | FStarC_Reflection_V2_Data.C_GTotal typ -> check typ
    | FStarC_Reflection_V2_Data.C_Lemma (pre, post, pats) ->
        let uu___ =
          let uu___1 = check pre in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.Tactics.CheckLN.fst"
                     (Prims.of_int (56)) (Prims.of_int (11))
                     (Prims.of_int (56)) (Prims.of_int (22)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.Tactics.CheckLN.fst"
                     (Prims.of_int (56)) (Prims.of_int (7))
                     (Prims.of_int (56)) (Prims.of_int (22)))))
            (Obj.magic uu___1)
            (fun uu___2 ->
               FStar_Tactics_Effect.lift_div_tac
                 (fun uu___3 -> Prims.op_Negation uu___2)) in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.CheckLN.fst"
                   (Prims.of_int (56)) (Prims.of_int (7)) (Prims.of_int (56))
                   (Prims.of_int (22)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.CheckLN.fst"
                   (Prims.of_int (56)) (Prims.of_int (4)) (Prims.of_int (58))
                   (Prims.of_int (14))))) (Obj.magic uu___)
          (fun uu___1 ->
             (fun uu___1 ->
                if uu___1
                then
                  Obj.magic
                    (Obj.repr
                       (FStar_Tactics_Effect.lift_div_tac
                          (fun uu___2 -> false)))
                else
                  Obj.magic
                    (Obj.repr
                       (let uu___3 =
                          let uu___4 = check post in
                          FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.CheckLN.fst"
                                     (Prims.of_int (57)) (Prims.of_int (11))
                                     (Prims.of_int (57)) (Prims.of_int (23)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.CheckLN.fst"
                                     (Prims.of_int (57)) (Prims.of_int (7))
                                     (Prims.of_int (57)) (Prims.of_int (23)))))
                            (Obj.magic uu___4)
                            (fun uu___5 ->
                               FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___6 -> Prims.op_Negation uu___5)) in
                        FStar_Tactics_Effect.tac_bind
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "FStar.Tactics.CheckLN.fst"
                                   (Prims.of_int (57)) (Prims.of_int (7))
                                   (Prims.of_int (57)) (Prims.of_int (23)))))
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "FStar.Tactics.CheckLN.fst"
                                   (Prims.of_int (57)) (Prims.of_int (4))
                                   (Prims.of_int (58)) (Prims.of_int (14)))))
                          (Obj.magic uu___3)
                          (fun uu___4 ->
                             (fun uu___4 ->
                                if uu___4
                                then
                                  Obj.magic
                                    (Obj.repr
                                       (FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___5 -> false)))
                                else Obj.magic (Obj.repr (check pats)))
                               uu___4)))) uu___1)
    | FStarC_Reflection_V2_Data.C_Eff (us, nm, res, args, decrs) ->
        let uu___ =
          let uu___1 = for_all check_u us in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.Tactics.CheckLN.fst"
                     (Prims.of_int (60)) (Prims.of_int (12))
                     (Prims.of_int (60)) (Prims.of_int (32)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.Tactics.CheckLN.fst"
                     (Prims.of_int (60)) (Prims.of_int (8))
                     (Prims.of_int (60)) (Prims.of_int (32)))))
            (Obj.magic uu___1)
            (fun uu___2 ->
               FStar_Tactics_Effect.lift_div_tac
                 (fun uu___3 -> Prims.op_Negation uu___2)) in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.CheckLN.fst"
                   (Prims.of_int (60)) (Prims.of_int (8)) (Prims.of_int (60))
                   (Prims.of_int (32)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.CheckLN.fst"
                   (Prims.of_int (60)) (Prims.of_int (5)) (Prims.of_int (64))
                   (Prims.of_int (9))))) (Obj.magic uu___)
          (fun uu___1 ->
             (fun uu___1 ->
                if uu___1
                then
                  Obj.magic
                    (Obj.repr
                       (FStar_Tactics_Effect.lift_div_tac
                          (fun uu___2 -> false)))
                else
                  Obj.magic
                    (Obj.repr
                       (let uu___3 =
                          let uu___4 = check res in
                          FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.CheckLN.fst"
                                     (Prims.of_int (61)) (Prims.of_int (12))
                                     (Prims.of_int (61)) (Prims.of_int (23)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.CheckLN.fst"
                                     (Prims.of_int (61)) (Prims.of_int (8))
                                     (Prims.of_int (61)) (Prims.of_int (23)))))
                            (Obj.magic uu___4)
                            (fun uu___5 ->
                               FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___6 -> Prims.op_Negation uu___5)) in
                        FStar_Tactics_Effect.tac_bind
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "FStar.Tactics.CheckLN.fst"
                                   (Prims.of_int (61)) (Prims.of_int (8))
                                   (Prims.of_int (61)) (Prims.of_int (23)))))
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "FStar.Tactics.CheckLN.fst"
                                   (Prims.of_int (61)) (Prims.of_int (5))
                                   (Prims.of_int (64)) (Prims.of_int (9)))))
                          (Obj.magic uu___3)
                          (fun uu___4 ->
                             (fun uu___4 ->
                                if uu___4
                                then
                                  Obj.magic
                                    (Obj.repr
                                       (FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___5 -> false)))
                                else
                                  Obj.magic
                                    (Obj.repr
                                       (let uu___6 =
                                          let uu___7 =
                                            for_all
                                              (fun uu___8 ->
                                                 match uu___8 with
                                                 | (a, q) -> check a) args in
                                          FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "FStar.Tactics.CheckLN.fst"
                                                     (Prims.of_int (62))
                                                     (Prims.of_int (12))
                                                     (Prims.of_int (62))
                                                     (Prims.of_int (49)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "FStar.Tactics.CheckLN.fst"
                                                     (Prims.of_int (62))
                                                     (Prims.of_int (8))
                                                     (Prims.of_int (62))
                                                     (Prims.of_int (49)))))
                                            (Obj.magic uu___7)
                                            (fun uu___8 ->
                                               FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___9 ->
                                                    Prims.op_Negation uu___8)) in
                                        FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "FStar.Tactics.CheckLN.fst"
                                                   (Prims.of_int (62))
                                                   (Prims.of_int (8))
                                                   (Prims.of_int (62))
                                                   (Prims.of_int (49)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "FStar.Tactics.CheckLN.fst"
                                                   (Prims.of_int (62))
                                                   (Prims.of_int (5))
                                                   (Prims.of_int (64))
                                                   (Prims.of_int (9)))))
                                          (Obj.magic uu___6)
                                          (fun uu___7 ->
                                             (fun uu___7 ->
                                                if uu___7
                                                then
                                                  Obj.magic
                                                    (Obj.repr
                                                       (FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___8 ->
                                                             false)))
                                                else
                                                  Obj.magic
                                                    (Obj.repr
                                                       (let uu___9 =
                                                          let uu___10 =
                                                            for_all check
                                                              decrs in
                                                          FStar_Tactics_Effect.tac_bind
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "FStar.Tactics.CheckLN.fst"
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (33)))))
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "FStar.Tactics.CheckLN.fst"
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (33)))))
                                                            (Obj.magic
                                                               uu___10)
                                                            (fun uu___11 ->
                                                               FStar_Tactics_Effect.lift_div_tac
                                                                 (fun uu___12
                                                                    ->
                                                                    Prims.op_Negation
                                                                    uu___11)) in
                                                        FStar_Tactics_Effect.tac_bind
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "FStar.Tactics.CheckLN.fst"
                                                                   (Prims.of_int (63))
                                                                   (Prims.of_int (8))
                                                                   (Prims.of_int (63))
                                                                   (Prims.of_int (33)))))
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "FStar.Tactics.CheckLN.fst"
                                                                   (Prims.of_int (63))
                                                                   (Prims.of_int (5))
                                                                   (Prims.of_int (64))
                                                                   (Prims.of_int (9)))))
                                                          (Obj.magic uu___9)
                                                          (fun uu___10 ->
                                                             FStar_Tactics_Effect.lift_div_tac
                                                               (fun uu___11
                                                                  ->
                                                                  if uu___10
                                                                  then false
                                                                  else true)))))
                                               uu___7)))) uu___4)))) uu___1)
and (check_br :
  FStar_Tactics_NamedView.branch ->
    (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun b ->
    let uu___ =
      Obj.magic (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> b)) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.CheckLN.fst"
               (Prims.of_int (68)) (Prims.of_int (15)) (Prims.of_int (68))
               (Prims.of_int (16)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.CheckLN.fst"
               (Prims.of_int (66)) (Prims.of_int (36)) (Prims.of_int (69))
               (Prims.of_int (9))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun uu___1 -> match uu___1 with | (p, t) -> Obj.magic (check t))
           uu___1)
let (check_ln :
  FStar_Tactics_NamedView.term ->
    (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  = fun t -> check t
let _ =
  FStarC_Tactics_Native.register_tactic "FStar.Tactics.CheckLN.check_ln"
    (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.CheckLN.check_ln (plugin)"
               (FStarC_Tactics_Native.from_tactic_1 check_ln)
               FStarC_Reflection_V2_Embeddings.e_term
               FStarC_Syntax_Embeddings.e_bool psc ncb us args)