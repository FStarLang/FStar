module Bug3213b

let forall_elim (#a: Type) (p: (a -> GTot prop)) (x:a)
  : Lemma (requires forall (x: a). p x) (ensures p x) = ()

[@@expect_failure [12]]
let also_bad ()
  : Lemma (forall (f : (nat -> Type0)). (forall (x : nat). f x) ==> (fun (_:nat) -> True) == f) = ()

[@@expect_failure [12]]
let also_bad_assumed ()
  : Lemma (forall (f : (nat -> Type0)). (forall (x : nat). f x) ==> (fun (_:nat) -> True) == f) = admit()
  
let eq_fun (f1 f2 : 'a -> 'b) (x : 'a) (_ : squash (f1 == f2)) : Lemma (f1 x == f2 x) = ()
  
// dedup_vc (FStarC.TypeChecker.Rel) collapses syntactically identical proof
// obligations, and the two `forall_elim` calls below raise the *same* one: the
// precondition `forall (x:a). p x` does not mention the explicit argument, so
// the obligations for `f0'` and `f1'` are literally the same formula. They are
// now reported once, hence two errors rather than three.
[@@expect_failure [19; 19]]
let bad2 () =
  let f0 : int -> prop = fun x -> True in
  let f1 : int -> prop = fun x -> x >= 0 in
  //also_bad_assumed (); -- now expect_failure
  let f0' : nat -> prop = f0 in
  let f1' : nat -> prop = f1 in
  forall_elim #(nat -> prop) (fun f -> (forall (x : nat). f x) ==> (fun (_:nat) -> True) == f) f0';
  forall_elim #(nat -> prop) (fun f -> (forall (x : nat). f x) ==> (fun (_:nat) -> True) == f) f1';
  assert (f0' == (fun (_:nat) -> True));
  assert (f1' == (fun (_:nat) -> True));
  assert (eq2 #(nat -> prop) f0' f0);
  assert (eq2 #(nat -> prop) f1' f1);
  assert (f0 == f1);
  eq_fun f0 f1 (-1) ();
  assert False;
  ()
