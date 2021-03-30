module Bug2229

open FStar.Tactics

(* A helper function to rewrite things *)
let rw (t:term): Tac unit =
  pointwise (fun () ->
    try (mapply t)
    with _ -> trefl ()
  )

assume val id: int -> int
assume val id_def: x:int -> Lemma
  (id x == x)

let test_ghost (x:int) (f:int -> Ghost (int) (requires True) (ensures fun _ -> True)): unit =
  assert (id (f x) == f x) by (
    rw(`id_def);
    trefl();
    qed()
  )

let test_pure_gtot (x:int) (f:int -> Pure (int) (requires True) (ensures fun _ -> True)) (g:int -> GTot int): unit =
  assert (id (f (g x)) == f (g x)) by (
    rw(`id_def);
    trefl();
    qed()
  )

let test_gtot(x:int) (f:int -> GTot int): unit =
  assert (id (f x) == f x) by (
    rw(`id_def);
    trefl();
    qed()
  )

let test_pure (x:int) (f:int -> Pure (int) (requires True) (ensures fun _ -> True)): unit =
  assert (id (f x) == f x) by (
    rw(`id_def);
    trefl();
    qed()
  )

let test_gtot_pure (x:int) (f:int -> GTot int) (g:int -> Pure (int) (requires True) (ensures fun _ -> True)): unit =
  assert (id (f (g x)) == f (g x)) by (
    rw(`id_def);
    trefl();
    qed()
  )
