module Prins

open FStar.OrdSet

assume new type prin : Type0

assume val p_cmp: f:(prin -> prin -> Tot bool){total_order prin f}

type eprins = ordset prin p_cmp

type prins = s:ordset prin p_cmp{size s > 0}

assume val ps_cmp: ps1:eprins -> ps2:eprins -> Tot bool (decreases (size ps1))

assume Ps_cmp_is_total_order: total_order prins ps_cmp

assume val all_prins: unit -> Tot prins

assume val all_prins_superset_lemma:
  unit -> Lemma (requires (True)) (ensures (forall ps. subset ps (all_prins ())))

