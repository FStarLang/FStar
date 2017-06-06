open Prims

(* Tactic extracted using --codegen OCaml *)
let user_print: Prims.string -> Prims.unit FStar_Tactics.tactic =
  fun s  ->
    Printf.printf "Running native code\n"; (* this line manually added for debugging *)
    FStar_Tactics.bind FStar_Tactics.get (fun ps  -> FStar_Tactics.return ())

(* handwritten invocation *)
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