module UnitTests

open FStar.Tactics

[@plugin]
let testnat (n:nat) : Tac nat = 42
