module FStarC.Misc

open FStarC
open FStarC.Effect
open FStarC.Util

open FStarC.Order
open FStar.String

let compare_version (v1 v2 : string) : order =
  let cs1 = String.split ['.'] v1 |> List.map int_of_string in
  let cs2 = String.split ['.'] v2 |> List.map int_of_string in
  compare_list cs1 cs2 compare_int

let version_gt v1 v2 = compare_version v1 v2 = Gt
let version_ge v1 v2 = compare_version v1 v2 <> Lt
