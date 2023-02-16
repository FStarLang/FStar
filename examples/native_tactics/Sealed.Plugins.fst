module Sealed.Plugins
open FStar.Sealed
open FStar.Tactics

[@@plugin]
let use_seal (s:sealed int) : Tac int = unseal s + 1

[@@plugin]
let get_seal (i:int) : sealed int = seal (i + 1)

[@@plugin]
let get_seal_tac (i:int) : Tac (sealed int) = seal (i + 1)



