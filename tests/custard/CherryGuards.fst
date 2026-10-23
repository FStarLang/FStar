module CherryGuards
module U32 = FStar.UInt32
open FStar.All

(* When clauses are only accepted without verification, as in the compiler's
   own sources, which are checked with --lax. *)
#set-options "--admit_smt_queries true"

let hide (#a: Type) (x: a) : ML a = x

(* Many guarded branches: each guard must not copy the branches after it. *)
let classify (x: int) : int =
  match x with
  | 0 -> 100
  | n when n = 1 -> 1 | n when n = 2 -> 2 | n when n = 3 -> 3
  | n when n = 4 -> 4 | n when n = 5 -> 5 | n when n = 6 -> 6
  | n when n = 7 -> 7 | n when n = 8 -> 8 | n when n = 9 -> 9
  | n when n = 10 -> 10 | n when n = 11 -> 11 | n when n = 12 -> 12
  | n when n = 13 -> 13 | n when n = 14 -> 14 | n when n = 15 -> 15
  | n when n = 16 -> 16 | n when n = 17 -> 17 | n when n = 18 -> 18
  | n when n = 19 -> 19 | n when n = 20 -> 20 | n when n = 21 -> 21
  | n when n = 22 -> 22 | n when n = 23 -> 23 | n when n = 24 -> 24
  | n when n = 25 -> 25 | n when n = 26 -> 26 | n when n = 27 -> 27
  | n when n = 28 -> 28 | n when n = 29 -> 29 | n when n = 30 -> 30
  | _ -> 0

let guards () : ML bool =
  classify (hide 0) = 100 && classify (hide 1) = 1 && classify (hide 17) = 17 &&
  classify (hide 30) = 30 && classify (hide 31) = 0

(* Guards on refutable patterns, and an option of a polymorphic value. *)
let first_pos (l: list int) : option int =
  match l with
  | x :: _ when x > 0 -> Some x
  | _ :: y :: _ when y > 0 -> Some y
  | [] -> None
  | _ -> Some 0

let refutable_guards () : ML bool =
  first_pos (hide [1; 2]) = Some 1 && first_pos (hide [0; 2]) = Some 2 &&
  first_pos (hide []) = None && first_pos (hide [0; 0]) = Some 0

(* Guarded exception handlers, as in FStarC.Errors.catch_errors_aux: a
   failing guard falls through to the later handlers, and an exception no
   handler takes is raised again. *)
exception Code of int
exception Other

let thrower (k: int) : ML int =
  if k = 0 then 0 else if k < 4 then raise (Code k) else raise Other

let handled (k: int) : ML int =
  try thrower k with
  | Code n when n = 1 -> 10
  | Code n when n = 2 -> 20

let outer (k: int) : ML int =
  try handled k with
  | Code _ -> 30
  | Other -> 40

let try_guards () : ML bool =
  outer (hide 0) = 0 && outer (hide 1) = 10 && outer (hide 2) = 20 &&
  outer (hide 3) = 30 && outer (hide 4) = 40

let main () : ML U32.t =
  if guards () && refutable_guards () && try_guards () then 0ul else 1ul
