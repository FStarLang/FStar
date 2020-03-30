module NestedLemma

assume
val p : nat -> prop

let test (n:nat) =
  let lem (x:nat)
    : Lemma
        (ensures p x)
        [SMTPat (p x)]
    = admit()
  in
  assert (p n)
