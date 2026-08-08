module FStar.Cardinality.Cantor

open FStar.Functions

let no_surj_powerset (a : Type) (f : a -> powerset a) : Lemma (~(is_surj f)) =
  let aux () : Lemma (requires is_surj f) (ensures False) =
    (* Cantor's proof: given a supposed surjective f,
    we define a set s that cannot be in the image of f. Namely,
    the set of x:a such that x is not in f(x).  *)
    let s : powerset a = fun x -> not (f x x) in
    lem_surj f s;
    // We obtain an x with f x == s, which means that f x x == not (f x x),
    // a contradiction.
    Classical.exists_elim False #a #(fun x -> f x == s) ()
      (fun x -> assert (f x x)) // this triggers the SMT appropriately
  in
  Classical.move_requires aux ()

let no_inj_powerset (a : Type) (f : powerset a -> a) : Lemma (~(is_inj f)) =
  let aux () : Lemma (requires is_inj f) (ensures False) =
    let g : a -> GTot (powerset a) = inverse_of_inj f (fun _ -> false) in
    no_surj_powerset a g
  in
  Classical.move_requires aux ()
