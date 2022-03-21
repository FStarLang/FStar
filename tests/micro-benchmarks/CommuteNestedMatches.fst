module CommuteNestedMatches

module T = FStar.Tactics

[@@ commute_nested_matches ]
type t =
 | A
 | B

let inner (b:bool) = if b then A else B

let outer (b:bool) =
  match inner b with
  | A -> 0
  | B -> 1

let opt (b:bool) = if b then 0 else 1

let test (b:bool) = assert (opt b == outer b) by T.trefl()

(* Without the attribute, the reflexivity proof fails *)
type s =
 | C
 | D

let inner_s (b:bool) = if b then C else D

let outer_s (b:bool) =
  match inner_s b with
  | C -> 0
  | D -> 1

let opt_s (b:bool) = if b then 0 else 1

[@@ expect_failure]
let test_s (b:bool) = assert (opt_s b == outer_s b) by T.trefl()
let test_s (b:bool) = assert (opt_s b == outer_s b) by T.smt()
