module Bug4252

[@@expect_failure [3]]
noeq
type t =
  | C : (unit -> Pure unit True (fun _ -> (exists (x:t). True) ==> False)) -> t

[@@expect_failure [3]]
noeq
type t' =
  | C : (unit -> Pure unit True (fun _ -> forall (x:t'). False)) -> t'

// let f1 (x : t) : Lemma False =
//   match x with
//   | C f -> f ()

// let f2 : False =
//   f1 (C (fun _ -> Classical.forall_intro f1))
