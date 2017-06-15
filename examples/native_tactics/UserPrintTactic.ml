open Prims
let user_print: Prims.string -> Prims.unit FStar_Tactics_Effect.tactic =
  fun s  ->
    FStar_Tactics_Effect.bind FStar_Tactics_Effect.get
      (fun ps  -> FStar_Tactics_Effect.return ())

let _ = FStar_Tactics_Native.register_tactic "UserPrintTactic.__user_print" 2
    (fun ps args ->
        FStar_Tactics_Interpreter.mk_tactic_interpretation_1
            ps
            (FStar_Tactics_Native.from_tactic_1 user_print)
            FStar_Reflection_Basic.unembed_string
            FStar_Reflection_Basic.embed_unit
            FStar_TypeChecker_Common.t_unit
            (FStar_Ident.lid_of_str "UserPrintTactic.__user_print")
            args)

let just_prune: Prims.unit FStar_Tactics_Effect.tactic =
  FStar_Tactics_Effect.bind (FStar_Tactics_Builtins.prune "")
    (fun uu___70_31  ->
        Printf.printf "Running native code\n"; (* this line manually added for debugging *)
        FStar_Tactics_Effect.return ())

(* handwritten invocation *)
let _ = FStar_Tactics_Native.register_tactic "UserPrintTactic.__just_prune" 1
    (fun ps args ->
        FStar_Tactics_Interpreter.mk_tactic_interpretation_0
            ps
            (FStar_Tactics_Native.from_tactic_0 just_prune)
            FStar_Reflection_Basic.embed_unit
            FStar_TypeChecker_Common.t_unit
            (FStar_Ident.lid_of_str "UserPrintTactic.__just_prune")
            args)
