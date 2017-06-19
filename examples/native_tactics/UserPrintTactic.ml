open Prims
let just_print: Prims.string -> Prims.unit FStar_Tactics_Effect.tactic =
  fun s  ->
    FStar_Tactics_Effect.bind (FStar_Tactics_Builtins.dump s)
      (fun uu___70_20  -> FStar_Tactics_Effect.return ())
let _ =
  FStar_Tactics_Native.register_tactic "UserPrintTactic.__just_print" 2
    (fun ps  ->
       fun args  ->
         FStar_Tactics_Interpreter.mk_tactic_interpretation_1 ps
           (FStar_Tactics_Native.from_tactic_1 just_print)
           FStar_Reflection_Basic.unembed_string
           FStar_Reflection_Basic.embed_unit FStar_TypeChecker_Common.t_unit
           (FStar_Ident.lid_of_str "UserPrintTactic.__just_print") args)