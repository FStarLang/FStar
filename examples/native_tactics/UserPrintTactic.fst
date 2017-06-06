module UserPrintTactic

open FStar.Tactics

let user_print (s: string): tactic unit =
    ps <-- get;
    return ()