module CoreBoolMatch

(* Core treats a match on a bool-typed scrutinee with both `true` and
   `false` constant branches as exhaustive without an SMT query.
   Incomplete matches must still be rejected: core_check_term defers its
   guard to the enclosing VC, which then fails. *)

open FStar.Tactics.V2

let check_ok (e t:term) : Tac unit =
  let g = top_env () in
  match core_check_term g e t E_Total with
  | Some _, _ -> ()
  | None, _ -> fail "expected core_check_term to succeed"

let ok1 = assert True by (check_ok (`(fun (b:bool) -> match b with | true -> 1 | false -> 0)) (`(bool -> int)))
let ok2 = assert True by (check_ok (`(fun (b:bool) -> match b with | false -> 1 | true -> 0)) (`(bool -> int)))
let rbool = b:bool{True}
let ok3 = assert True by (check_ok (`(fun (b:rbool) -> match b with | true -> 1 | false -> 0)) (`(rbool -> int)))
let ok4 = assert True by (check_ok (`(fun (b:bool) -> match b with | true -> 1 | true -> 2 | false -> 0)) (`(bool -> int)))

[@@expect_failure [19]]
let bad1 = assert True by (check_ok (`(fun (b:bool) -> match b with | true -> 1)) (`(bool -> int)))
[@@expect_failure [19]]
let bad2 = assert True by (check_ok (`(fun (b:bool) -> match b with | false -> 1 | false -> 0)) (`(bool -> int)))
[@@expect_failure [19]]
let bad3 = assert True by (check_ok (`(fun (b:bool) -> match b with | true -> 1 | true -> 0)) (`(bool -> int)))
