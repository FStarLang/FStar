module Bug4615

(* The local closure [aux] used to exhaust its rlimit, or not return at all:
   the goal walker assumed proven sibling conjuncts such as [bnd ...], whose
   definitions hide quantifiers. *)

module Seq = FStar.Seq
module Math = FStar.Math.Lemmas

let rad : pos = 64
let base : pos = pow2 rad

let rec eval (s: Seq.seq nat) : Tot nat (decreases Seq.length s) =
  let n = Seq.length s in
  if n = 0 then 0
  else Seq.index s 0 + base * eval (Seq.slice s 1 n)

let bnd (s: Seq.seq nat) (c: nat) : prop =
  forall (i: nat). i < Seq.length s ==> Seq.index s i < c

let limbs_n (x: nat) (n: nat) : Seq.seq nat =
  Seq.init #nat n (fun i -> x / pow2 (rad * i) % base)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 400"
let rec limbs_n_eval (x: nat) (n: nat)
  : Lemma (ensures Seq.length (limbs_n x n) == n /\ bnd (limbs_n x n) base /\
                   eval (limbs_n x n) == x % pow2 (rad * n))
          (decreases n)
  = if n = 0 then ()
    else begin
      limbs_n_eval (x / base) (n - 1);
      let t = Seq.slice (limbs_n x n) 1 n in
      let aux (i: nat { i < n - 1 })
        : Lemma (Seq.index t i == Seq.index (limbs_n (x / base) (n - 1)) i)
        = Math.pow2_plus rad (rad * i);
          Math.division_multiplication_lemma x base (pow2 (rad * i)) in
      Classical.forall_intro aux;
      Seq.lemma_eq_intro t (limbs_n (x / base) (n - 1));
      Math.distributivity_add_right rad 1 (n - 1);
      assert (rad * n == rad + rad * (n - 1));
      Math.pow2_plus rad (rad * (n - 1));
      assert (pow2 (rad * n) == base * pow2 (rad * (n - 1)));
      Math.modulo_division_lemma x base (pow2 (rad * (n - 1)));
      Math.euclidean_division_definition (x % pow2 (rad * n)) base;
      Math.pow2_modulo_modulo_lemma_1 x rad (rad * n)
    end
#pop-options
