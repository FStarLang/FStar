module Bug2398

#push-options "--fuel 0 --ifuel 0 --warn_error -328"
assume
val seq : Type0 -> Type0

let rec map (f: nat -> nat)
            (s: seq nat)
  : Tot (seq nat)
  = s

//mark it recursive, even though it really isn't
let rec t2_to_t1 (x: nat) : Tot nat = 0

let pat (x y:seq nat) : nat = 0

let t2_to_t1_equivalent_to_map (x: seq nat) (y:seq nat)
  : Lemma (ensures (map t2_to_t1 x == y))
          [SMTPat (pat x y)] //this is just to force the lemma to be SMT encoded
  = admit()

let rec t2_to_t1_alt (x y: nat) : Tot nat = 0

let t2_to_t1_alt_equivalent_to_map (x: seq nat) (y:seq nat)
  : Lemma (ensures (map (t2_to_t1_alt 0) x == y))
          [SMTPat (pat x y)] //this is just to force the lemma to be SMT encoded
  = admit()

//This is just to trigger an SMT query
let test (x:nat) = assert (x >= 0)
