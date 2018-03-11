module Print

open FStar.Tactics

[@plugin]
let just_print (s: string): Tac unit =
    dump s
