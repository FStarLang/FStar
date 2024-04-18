module FStar.Cardinality.Cantor

open FStar.Functions

let no_surj_powerset (a : Type) (f : a -> powerset a) : Lemma (~(is_surj f)) =
  let aux () : Lemma (requires is_surj f) (ensures False) =
    (* Cantor's proof: given a supposed surjective f,
    we define a set s that cannot be in the image of f. Namely,
    the set of x:a such that x is not in f(x).  *)
    let s : powerset a = fun x -> not (f x x) in
    let aux (x : a) : Lemma (requires f x == s) (ensures False) =
      // We have f x == s, which means that f x x == not (f x x), contradiction
      assert (f x x) // this triggers the SMT appropriately
    in
    Classical.forall_intro (Classical.move_requires aux)
  in
  Classical.move_requires aux ()

let no_inj_powerset (a : Type) (f : powerset a -> a) : Lemma (~(is_inj f)) =
  let aux () : Lemma (requires is_inj f) (ensures False) =
    let g : a -> powerset a = inverse_of_inj f (fun _ -> false) in
    no_surj_powerset a g
  in
  Classical.move_requires aux ()
