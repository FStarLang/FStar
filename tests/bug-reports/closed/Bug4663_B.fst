module Bug4663_B

(* #4663: [Rel] decided [Mkst?.f #nat (kf #nat s) = Mkst?.f #word (kf #word s)]
   by reducing both sides to head normal form and recursing into the arguments.
   That unfolds [kf], and since [r0] uses its argument twice, every level of the
   call graph doubled the work; this never finished. Congruence decides it by
   comparing [nat] with the abbreviation [word]. *)

open Bug4663_A

let lemma_probe (s: st word) (k: nat) (y: Seq.seq word)
  : Lemma (requires Seq.length y > k)
          (ensures (let s' = kf #word s in g s'.f k y >= 0))
  = ()

(* The same equation, reached directly by subtyping. *)
assume val t : Seq.seq nat -> Type0

let coerce (s: st word) (x: t (kf #nat s).f) : t (kf #word s).f = x
