module Bug1535b

[@(expect_failure [3])]
exception E1 of (exn -> int)

[@(expect_failure [3])]
exception E2 of (exn -> exn)

[@(expect_failure [3])]
exception E3 of ((exn -> int) -> int)

[@(expect_failure [3])]
exception E4 of exn * (exn -> int)

[@(expect_failure [3])]
exception E5 of exn * (exn -> exn)

(* Here's how to exploit it if it succeeded: *)

// let f (e:exn) : exn =
//   match e with
//   | E1 f -> f e
//   | e -> e
//
// let g : exn = E1 f
//
// let h = f (E1 f) (* would loop on execution *)

(* Good ones *)
exception G0 of int
exception G1 of exn
exception G2 of (int -> exn)
exception G3 of (int -> exn * exn)
exception G4 of (int -> exn) * exn
