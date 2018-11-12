module ErrorMsg

(* Works *)
let rec factorial (x:nat) : nat =
  match x with
    | 0 -> 1
    | _ -> x + factorial (x - 1)

//(Error) Subtyping check failed; expected type x:nat{x << x}; got type int
[@expect_failure]
let rec factorial2 (x:nat) : nat =
  match x with
    | 0 -> 1
    | _ -> x + factorial2 (x - 2)

//(Error) Could not prove termination of this recursive call
[@expect_failure]
let rec factorial3 (x:nat) : Tot nat =
  match x with
    | 0 -> 1
    | _ -> x + factorial3 x
