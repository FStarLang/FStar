module Bug4591

module Seq = FStar.Seq
module Math = FStar.Math.Lemmas

let rad : pos = 64
let base : pos = pow2 rad

#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"

let rec eval (s: Seq.seq nat) : Tot nat (decreases Seq.length s) =
  let n = Seq.length s in
  if n = 0 then 0
  else Seq.index s 0 + base * eval (Seq.slice s 1 n)

// An unused lemma above [eval_split] used to be enough to push its final
// goal past the rlimit (issue #4591): the sign facts [eval _ >= 0] and
// [pow2 _ > 0] of the lemma arguments were not in the VC.
let eval_empty (s: Seq.seq nat) : Lemma (requires Seq.length s == 0) (ensures eval s == 0) = ()

let rec eval_split (s: Seq.seq nat) (k: nat { k <= Seq.length s })
  : Lemma (ensures eval s == eval (Seq.slice s 0 k) +
                             pow2 (rad * k) * eval (Seq.slice s k (Seq.length s)))
          (decreases k)
  = let n = Seq.length s in
    if k = 0 then Seq.lemma_eq_intro (Seq.slice s 0 n) s
    else begin
      let t = Seq.slice s 1 n in
      eval_split t (k - 1);
      Seq.lemma_eq_intro (Seq.slice t 0 (k - 1)) (Seq.slice (Seq.slice s 0 k) 1 k);
      Seq.lemma_eq_intro (Seq.slice t (k - 1) (n - 1)) (Seq.slice s k n);
      Math.pow2_plus rad (rad * (k - 1));
      Math.distributivity_add_right base (eval (Seq.slice t 0 (k - 1)))
        (pow2 (rad * (k - 1)) * eval (Seq.slice s k n));
      Math.paren_mul_right base (pow2 (rad * (k - 1))) (eval (Seq.slice s k n))
    end
#pop-options
