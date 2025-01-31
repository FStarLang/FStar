open Fstarcompiler
open FStarC_Tactics_Result
open FStarC_Tactics_Types

let tac_return x = fun ps -> Success (x, ps)

let unseal x = tac_return x
