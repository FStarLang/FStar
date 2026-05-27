module Bug3213

let forall_elim (#a: Type) (p: (a -> GTot prop)) (x:a)
  : Lemma (requires forall (x: a). p x) (ensures p x) = ()

[@@expect_failure [12]]
let bad ()
  : Lemma (forall (f : int -> Type0). (forall (x : nat). f x) ==> f (-1)) = ()

[@@expect_failure [12]]
let bad_assumed ()
  : Lemma (forall (f : int -> Type0). (forall (x : nat). f x) ==> f (-1)) = admit()

[@@expect_failure [12; 34]]
let falso () : Lemma False =
  let f (x:int) : Type0 = x >= 0 in
  forall_elim #(int -> Type0) (fun f -> (forall (x : nat). f x) ==> f (-1)) f;
  ()
