module UserPrintTactic

open FStar.Tactics.Effect

let user_print (s: string): tactic unit =
    ps <-- get;
    return ()