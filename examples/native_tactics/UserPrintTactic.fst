module UserPrintTactic

open FStar.Tactics

let just_print (s: string): tactic unit =
    dump s;;
    return ()