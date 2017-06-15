module UserPrintTactic

open FStar.Tactics

let user_print (s: string): tactic unit =
    ps <-- get;
    return ()

let just_prune: tactic unit =
    dump "state: ";;
    return ()