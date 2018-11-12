module Bug380_2
let single_inhabitant t = 
  forall (x y: t). x == y

let single_inhabitant_and p q
    : Lemma (single_inhabitant (p /\ q)) = ()

let single_inhabitant_bool ()
    : Lemma (single_inhabitant bool) =
  let should_fail = assert (bool == (True /\ bool)) in // Woops.  The normalizer used to simplifies `True /\ bool` into bool instead of `squash bool`
  single_inhabitant_and True bool

let falso () : Lemma False =
  single_inhabitant_bool ();
  assert (true == false)
