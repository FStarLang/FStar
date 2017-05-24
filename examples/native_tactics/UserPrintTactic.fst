module UserPrintTactic

open FStar.Tactics

(* Original tactic written by the user and extracted to UserPrintTac.ml *)
(*
let user_print (s: string): tactic unit =
    ps <-- get;
    return ()
*)

assume val __user_print: string -> __tac unit
let user_print (s:string) : tactic unit = fun () -> TAC?.reflect (__user_print s)
