open Prims
open FStar_Reflection_Basic
open FStar_Syntax_Syntax
open FStar_Syntax_Const
open FStar_Tactics_Embedding

let __user_print : Prims.string -> Prims.unit FStar_Tactics.__tac =
    FStar_Tactics.bind FStar_Tactics.get (fun ps  -> FStar_Tactics.return ())
let user_print : Prims.string -> Prims.unit -> Prims.unit FStar_Tactics.__tac
  = fun s  -> fun uu____24  -> __user_print s 

let _ =
  FStar_Tactics_Native.register_tactic "UserPrintTactic.__user_print" 2 (fun ps args ->
    FStar_Tactics_Interpreter.mk_tactic_interpretation_1 ps
    (FStar_Tactics_Native.from_tactic_1 user_print)
    unembed_string embed_unit FStar_TypeChecker_Common.t_unit
    (FStar_Ident.lid_of_str "UserPrintTactic.__user_print") args)
