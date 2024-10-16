open Prims
exception Appears 
let (uu___is_Appears : Prims.exn -> Prims.bool) =
  fun projectee -> match projectee with | Appears -> true | uu___ -> false
let (name_appears_in :
  FStarC_Reflection_Types.name ->
    FStar_Tactics_NamedView.term ->
      (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun nm ->
    fun t ->
      let uu___ =
        Obj.magic
          (FStar_Tactics_Effect.lift_div_tac
             (fun uu___1 ->
                fun t1 ->
                  let uu___2 = FStar_Tactics_NamedView.inspect t1 in
                  FStar_Tactics_Effect.tac_bind
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "FStar.Tactics.Names.fst"
                             (Prims.of_int (15)) (Prims.of_int (10))
                             (Prims.of_int (15)) (Prims.of_int (19)))))
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "FStar.Tactics.Names.fst"
                             (Prims.of_int (15)) (Prims.of_int (4))
                             (Prims.of_int (20)) (Prims.of_int (12)))))
                    (Obj.magic uu___2)
                    (fun uu___3 ->
                       (fun uu___3 ->
                          match uu___3 with
                          | FStar_Tactics_NamedView.Tv_FVar fv ->
                              Obj.magic
                                (Obj.repr
                                   (let uu___4 =
                                      if
                                        (FStarC_Reflection_V2_Builtins.inspect_fv
                                           fv)
                                          = nm
                                      then
                                        Obj.magic
                                          (FStar_Tactics_Effect.raise Appears)
                                      else
                                        Obj.magic
                                          (FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___6 -> ())) in
                                    FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "FStar.Tactics.Names.fst"
                                               (Prims.of_int (17))
                                               (Prims.of_int (6))
                                               (Prims.of_int (18))
                                               (Prims.of_int (21)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "FStar.Tactics.Names.fst"
                                               (Prims.of_int (14))
                                               (Prims.of_int (10))
                                               (Prims.of_int (14))
                                               (Prims.of_int (11)))))
                                      (Obj.magic uu___4)
                                      (fun uu___5 ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___6 -> t1))))
                          | uu___4 ->
                              Obj.magic
                                (Obj.repr
                                   (FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___5 -> t1)))) uu___3))) in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.Names.fst"
                 (Prims.of_int (15)) (Prims.of_int (4)) (Prims.of_int (20))
                 (Prims.of_int (12)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.Names.fst"
                 (Prims.of_int (22)) (Prims.of_int (2)) (Prims.of_int (25))
                 (Prims.of_int (20))))) (Obj.magic uu___)
        (fun uu___1 ->
           (fun ff ->
              let uu___1 =
                FStarC_Tactics_V2_Builtins.catch
                  (fun uu___2 ->
                     let uu___3 =
                       let uu___4 = FStar_Tactics_Visit.visit_tm ff t in
                       FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.Tactics.Names.fst"
                                  (Prims.of_int (22)) (Prims.of_int (32))
                                  (Prims.of_int (22)) (Prims.of_int (49)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.Tactics.Names.fst"
                                  (Prims.of_int (22)) (Prims.of_int (25))
                                  (Prims.of_int (22)) (Prims.of_int (49)))))
                         (Obj.magic uu___4)
                         (fun uu___5 ->
                            FStar_Tactics_Effect.lift_div_tac
                              (fun uu___6 -> ())) in
                     FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "FStar.Tactics.Names.fst"
                                (Prims.of_int (22)) (Prims.of_int (25))
                                (Prims.of_int (22)) (Prims.of_int (49)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "FStar.Tactics.Names.fst"
                                (Prims.of_int (22)) (Prims.of_int (51))
                                (Prims.of_int (22)) (Prims.of_int (56)))))
                       (Obj.magic uu___3)
                       (fun uu___4 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___5 -> false))) in
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.Names.fst"
                            (Prims.of_int (22)) (Prims.of_int (8))
                            (Prims.of_int (22)) (Prims.of_int (57)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.Names.fst"
                            (Prims.of_int (22)) (Prims.of_int (2))
                            (Prims.of_int (25)) (Prims.of_int (20)))))
                   (Obj.magic uu___1)
                   (fun uu___2 ->
                      match uu___2 with
                      | FStar_Pervasives.Inr x ->
                          FStar_Tactics_Effect.lift_div_tac (fun uu___3 -> x)
                      | FStar_Pervasives.Inl (Appears) ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___3 -> true)
                      | FStar_Pervasives.Inl e ->
                          FStar_Tactics_Effect.raise e))) uu___1)
let _ =
  FStarC_Tactics_Native.register_tactic "FStar.Tactics.Names.name_appears_in"
    (Prims.of_int (3))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_2
               "FStar.Tactics.Names.name_appears_in (plugin)"
               (FStarC_Tactics_Native.from_tactic_2 name_appears_in)
               (FStarC_Syntax_Embeddings.e_list
                  FStarC_Syntax_Embeddings.e_string)
               FStarC_Reflection_V2_Embeddings.e_term
               FStarC_Syntax_Embeddings.e_bool psc ncb us args)