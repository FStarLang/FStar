module LowStar.Modifies.Linear

open LowStar.Monotonic.Buffer

module HS = FStar.HyperStack

let modifies_trans_linear (s l:loc) (h1 h2 h3:HS.mem)
  : Lemma (requires (modifies s h1 h2 /\ modifies l h2 h3 /\ loc_includes l s))
          (ensures  (modifies l h1 h3))
	  [SMTPat (modifies s h1 h2); SMTPat (modifies l h1 h3)]
  = ()
