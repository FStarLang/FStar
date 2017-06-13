open Prims
let user_print: Prims.string -> Prims.unit FStar_Tactics_Effect.tactic =
  fun s  ->
    FStar_Tactics_Effect.bind FStar_Tactics_Effect.get
      (fun ps  -> FStar_Tactics_Effect.return ())
let _ =
  FStar_Tactics.Native.register_tactic "UserPrintTactic.__user_print"
    (Prims.parse_int "1") ()