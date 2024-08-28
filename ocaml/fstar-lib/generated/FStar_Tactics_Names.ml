open Prims
exception Appears 
let (uu___is_Appears : Prims.exn -> Prims.bool) =
  fun projectee -> match projectee with | Appears -> true | uu___ -> false
let (name_appears_in :
  FStar_Reflection_Types.name ->
    FStar_Tactics_NamedView.term ->
      (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun nm ->
    fun t ->
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
                 (Prims.of_int (20)))))
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___ ->
              fun t1 ->
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
                  (Obj.magic (FStar_Tactics_NamedView.inspect t1))
                  (fun uu___1 ->
                     (fun uu___1 ->
                        match uu___1 with
                        | FStar_Tactics_NamedView.Tv_FVar fv ->
                            Obj.magic
                              (Obj.repr
                                 (FStar_Tactics_Effect.tac_bind
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
                                    (if
                                       (FStar_Reflection_V2_Builtins.inspect_fv
                                          fv)
                                         = nm
                                     then FStar_Tactics_Effect.raise Appears
                                     else
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___3 -> ()))
                                    (fun uu___2 ->
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___3 -> t1))))
                        | uu___2 ->
                            Obj.magic
                              (Obj.repr
                                 (FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___3 -> t1)))) uu___1)))
        (fun uu___ ->
           (fun ff ->
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
                   (Obj.magic
                      (FStar_Tactics_V2_Builtins.catch
                         (fun uu___ ->
                            FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "FStar.Tactics.Names.fst"
                                       (Prims.of_int (22))
                                       (Prims.of_int (25))
                                       (Prims.of_int (22))
                                       (Prims.of_int (49)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "FStar.Tactics.Names.fst"
                                       (Prims.of_int (22))
                                       (Prims.of_int (51))
                                       (Prims.of_int (22))
                                       (Prims.of_int (56)))))
                              (Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.Tactics.Names.fst"
                                             (Prims.of_int (22))
                                             (Prims.of_int (32))
                                             (Prims.of_int (22))
                                             (Prims.of_int (49)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.Tactics.Names.fst"
                                             (Prims.of_int (22))
                                             (Prims.of_int (25))
                                             (Prims.of_int (22))
                                             (Prims.of_int (49)))))
                                    (Obj.magic
                                       (FStar_Tactics_Visit.visit_tm ff t))
                                    (fun uu___1 ->
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___2 -> ()))))
                              (fun uu___1 ->
                                 FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___2 -> false)))))
                   (fun uu___ ->
                      match uu___ with
                      | FStar_Pervasives.Inr x ->
                          FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> x)
                      | FStar_Pervasives.Inl (Appears) ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___1 -> true)
                      | FStar_Pervasives.Inl e ->
                          FStar_Tactics_Effect.raise e))) uu___)
let _ =
  FStar_Tactics_Native.register_tactic "FStar.Tactics.Names.name_appears_in"
    (Prims.of_int (3))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStar_Tactics_InterpFuns.mk_tactic_interpretation_2
               "FStar.Tactics.Names.name_appears_in (plugin)"
               (FStar_Tactics_Native.from_tactic_2 name_appears_in)
               (FStar_Syntax_Embeddings.e_list
                  FStar_Syntax_Embeddings.e_string)
               FStar_Reflection_V2_Embeddings.e_term
               FStar_Syntax_Embeddings.e_bool psc ncb us args)