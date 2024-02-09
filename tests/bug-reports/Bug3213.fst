module Bug3213

#set-options "--debug Test --debug_level SMTQuery"

let ff = nat -> Type0

let bad2 ()
  : Lemma (forall (f : ff). (forall (x : nat). f x) ==> (fun (_:nat) -> True) == f) = ()

[@@expect_failure [19]]
let bad ()
  : Lemma (forall (f : int -> Type0). (forall (x : nat). f x) ==> f (-1)) = ()

(* Replaying unsoundness from an axiom *)
let bad_assumed ()
  : Lemma (forall (f : int -> Type0). (forall (x : nat). f x) ==> f (-1)) = admit()

let forall_elim (#a: Type) (p: (a -> GTot Type)) (x:a)
  : Lemma (requires forall (x: a). p x) (ensures p x) = ()

let falso () : Lemma False =
  bad_assumed();
  let f (x:int) : Type0 = x >= 0 in
  forall_elim #(int -> Type0) (fun f -> (forall (x : nat). f x) ==> f (-1)) f;
  ()
