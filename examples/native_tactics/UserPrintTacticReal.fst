module UserPrintTactic

open FStar.Tactics

let __user_print (s: string): tactic unit =
    ps <-- get;
    return ()
