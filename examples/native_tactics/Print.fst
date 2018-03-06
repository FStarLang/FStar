module Print

open FStar.Tactics

let just_print (s: string): Tac unit =
    dump s
