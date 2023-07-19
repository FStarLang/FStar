open Prims
let (terms_to_string :
  Pulse_Syntax_Base.term Prims.list ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Checker.fst" (Prims.of_int (38))
               (Prims.of_int (23)) (Prims.of_int (38)) (Prims.of_int (68)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Pulse.Checker.fst" (Prims.of_int (38))
               (Prims.of_int (4)) (Prims.of_int (38)) (Prims.of_int (68)))))
      (Obj.magic
         (FStar_Tactics_Util.map Pulse_Syntax_Printer.term_to_string t))
      (fun uu___ ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___1 -> FStar_String.concat "\n" uu___))
let (has_pure_vprops : Pulse_Syntax_Base.term -> Prims.bool) =
  fun pre ->
    FStar_List_Tot_Base.existsb
      (fun t -> Pulse_Syntax_Base.uu___is_Tm_Pure t.Pulse_Syntax_Base.t)
      (Pulse_Typing_Combinators.vprop_as_list pre)
let (elim_pure_explicit_lid : Prims.string Prims.list) =
  Pulse_Reflection_Util.mk_steel_wrapper_lid "elim_pure_explicit"
let (default_binder_annot : Pulse_Syntax_Base.binder) =
  {
    Pulse_Syntax_Base.binder_ty = Pulse_Syntax_Base.tm_unknown;
    Pulse_Syntax_Base.binder_ppname = Pulse_Syntax_Base.ppname_default
  }
let rec (check' : Prims.bool -> Pulse_Checker_Common.check_t) =
  fun allow_inst ->
    fun g ->
      fun pre ->
        fun pre_typing ->
          fun post_hint ->
            fun t ->
              FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Checker.fst"
                         (Prims.of_int (338)) (Prims.of_int (12))
                         (Prims.of_int (338)) (Prims.of_int (55)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Pulse.Checker.fst"
                         (Prims.of_int (340)) (Prims.of_int (6))
                         (Prims.of_int (354)) (Prims.of_int (50)))))
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___ ->
                      Pulse_Checker_Pure.push_context
                        (Pulse_Syntax_Printer.tag_of_st_term t)
                        t.Pulse_Syntax_Base.range2 g))
                (fun uu___ ->
                   (fun g1 ->
                      match t.Pulse_Syntax_Base.term1 with
                      | Pulse_Syntax_Base.Tm_Protect uu___ ->
                          Obj.magic
                            (Obj.repr
                               (FStar_Tactics_V2_Derived.fail
                                  "Protect should have been removed"))
                      | Pulse_Syntax_Base.Tm_Return uu___ ->
                          Obj.magic
                            (Obj.repr
                               (Pulse_Checker_Return.check_return g1 t pre ()
                                  post_hint))
                      | Pulse_Syntax_Base.Tm_Abs uu___ ->
                          Obj.magic
                            (Obj.repr
                               (FStar_Tactics_V2_Derived.fail
                                  "Tm_Abs check should not have been called in the checker"))
                      | Pulse_Syntax_Base.Tm_STApp uu___ ->
                          Obj.magic
                            (Obj.repr
                               (Pulse_Checker_STApp.check_stapp g1 t pre ()
                                  post_hint))
                      | Pulse_Syntax_Base.Tm_Bind uu___ ->
                          Obj.magic
                            (Obj.repr
                               (Pulse_Checker_Bind.check_bind g1 t pre ()
                                  post_hint (check' true)))
                      | uu___ ->
                          Obj.magic
                            (Obj.repr
                               (FStar_Tactics_V2_Derived.fail
                                  "Checker form not implemented"))) uu___)
let (check : Pulse_Checker_Common.check_t) = check' true