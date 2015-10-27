(*--build-config
    options:--admit_fsi FStar.OrdSet;
    other-files:ordset.fsi
 --*)

module Prins

open FStar.OrdSet

type prin

val p_cmp: f:(prin -> prin -> Tot bool){total_order prin f}

type eprins = ordset prin p_cmp

type prins = s:ordset prin p_cmp{size s > 0}

val ps_cmp: ps1:eprins -> ps2:eprins -> Tot bool (decreases (size ps1))

assume Ps_cmp_is_total_order: total_order prins ps_cmp

val all_prins: unit -> Tot prins

val all_prins_superset_lemma:
  unit -> Lemma (requires (True)) (ensures (forall ps. subset ps (all_prins ())))

