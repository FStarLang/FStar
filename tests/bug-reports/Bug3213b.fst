module Bug3213b

let forall_elim (#a: Type) (p: (a -> GTot Type)) (x:a)
  : Lemma (requires forall (x: a). p x) (ensures p x) = ()

[@@expect_failure [19]]
let also_bad ()
  : Lemma (forall (f : (nat -> Type0)). (forall (x : nat). f x) ==> (fun (_:nat) -> True) == f) = ()

let also_bad_assumed ()
  : Lemma (forall (f : (nat -> Type0)). (forall (x : nat). f x) ==> (fun (_:nat) -> True) == f) = admit()
  
let eq_fun (f1 f2 : 'a -> 'b) (x : 'a) (_ : squash (f1 == f2)) : Lemma (f1 x == f2 x) = ()
  
let bad2 () =
  let f0 : int -> Type0 = fun x -> True in
  let f1 : int -> Type0 = fun x -> x >= 0 in
  also_bad_assumed ();
  let f0' : nat -> Type0 = f0 in
  let f1' : nat -> Type0 = f1 in
  forall_elim #(nat -> Type0) (fun f -> (forall (x : nat). f x) ==> (fun (_:nat) -> True) == f) f0';
  forall_elim #(nat -> Type0) (fun f -> (forall (x : nat). f x) ==> (fun (_:nat) -> True) == f) f1';
  assert (f0' == (fun (_:nat) -> True));
  assert (f1' == (fun (_:nat) -> True));
  assert (eq2 #(nat -> Type0) f0' f0);
  assert (eq2 #(nat -> Type0) f1' f1);
  assert (f0 == f1);
  eq_fun f0 f1 (-1) ();
  assert False;
  ()
