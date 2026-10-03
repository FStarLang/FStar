module Bug3213

let forall_elim (#a: Type) (p: (a -> GTot prop)) (x:a)
  : Lemma (requires forall (x: a). p x) (ensures p x) = ()

[@@expect_failure [12]]
let bad ()
  : Lemma (forall (f : int -> Type0). (forall (x : nat). f x) ==> f (-1)) = ()

[@@expect_failure [12]]
let bad_assumed ()
  : Lemma (forall (f : int -> Type0). (forall (x : nat). f x) ==> f (-1)) = admit()

(* Both arguments are rejected on their own terms.  Recovery from the first
   subtyping failure used to leave a computation type whose result was still the
   rejected [Type0], which then re-surfaced as a "computed type ... is not
   compatible with the annotated type" (34) against the [GTot prop] annotation
   and hid the second argument's error. *)
[@@expect_failure [12; 12]]
let falso () : Lemma False =
  let f (x:int) : Type0 = x >= 0 in
  forall_elim #(int -> Type0) (fun f -> (forall (x : nat). f x) ==> f (-1)) f;
  ()
