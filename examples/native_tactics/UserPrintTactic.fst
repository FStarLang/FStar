module UserPrintTactic

open FStar.Tactics

assume val __user_print: string -> __tac unit
let user_print (s:string) : tactic unit = fun () -> TAC?.reflect (__user_print s)
