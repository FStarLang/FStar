(*--build-config
    options:--admit_fsi FStar.OrdSet;
    other-files:ordset.fsi prins.fsi
 --*)

module Prins

open FStar.OrdSet

type prin =
  | Alice
  | Bob
  | Charlie
  | Dave
  | Evelyn
  | Fred

(* TODO: FIXME: we should not write this type *)
val p_cmp: prin -> prin -> Tot bool
let p_cmp p1 p2 =
       if p1 = Alice   then true
  else if p1 = Bob     then not (p2 = Alice)
  else if p1 = Charlie then not (p2 = Alice || p2 = Bob)
  else if p1 = Dave    then not (p2 = Alice || p2 = Bob || p2 = Charlie)
  else if p1 = Evelyn  then not (p2 = Alice || p2 = Bob || p2 = Charlie || p2 = Dave)
  else                      not (p2 = Alice || p2 = Bob || p2 = Charlie || p2 = Dave || p2 = Evelyn)

type eprins = ordset prin p_cmp

type prins = s:ordset prin p_cmp{not (s = empty)}

val ps_cmp: ps1:eprins -> ps2:eprins -> Tot bool (decreases (size ps1))
let rec ps_cmp ps1 ps2 =
  if size ps1 < size ps2 then false
  else if size ps1 > size ps2 then true
  else
    if ps1 = empty && ps2 = empty then true
    else
      let Some p1, Some p2 = choose ps1, choose ps2 in
      let ps1_rest, ps2_rest = remove p1 ps1, remove p2 ps2 in
      if p1 = p2 then ps_cmp ps1_rest ps2_rest
      else p_cmp p1 p2

val ps_cmp_antisymm:
  ps1:eprins -> ps2:eprins
  -> Lemma (requires (True)) (ensures ((ps_cmp ps1 ps2 /\ ps_cmp ps2 ps1) ==> ps1 = ps2))
     (decreases (size ps1))
let rec ps_cmp_antisymm ps1 ps2 =
  if ps1 = empty || ps2 = empty then ()
  else
    let Some p1, Some p2 = choose ps1, choose ps2 in
    let ps1_rest, ps2_rest = remove p1 ps1, remove p2 ps2 in
    ps_cmp_antisymm ps1_rest ps2_rest

val ps_cmp_trans:
  ps1:eprins -> ps2:eprins -> ps3:eprins
  -> Lemma (requires (True)) (ensures ((ps_cmp ps1 ps2 /\ ps_cmp ps2 ps3) ==> ps_cmp ps1 ps3))
     (decreases (size ps1))
let rec ps_cmp_trans ps1 ps2 ps3 =
  if ps1 = empty || ps2 = empty || ps3 = empty then ()
  else
    let Some p1, Some p2, Some p3 = choose ps1, choose ps2, choose ps3 in
    let ps1_rest, ps2_rest, ps3_rest = remove p1 ps1, remove p2 ps2, remove p3 ps3 in
    ps_cmp_trans ps1_rest ps2_rest ps3_rest

val ps_cmp_total:
  ps1:eprins -> ps2:eprins
  -> Lemma (requires (True)) (ensures (ps_cmp ps1 ps2 \/ ps_cmp ps2 ps1))
     (decreases (size ps1))
let rec ps_cmp_total ps1 ps2 =
  if ps1 = empty || ps2 = empty then ()
  else
    let Some p1, Some p2 = choose ps1, choose ps2 in
    let ps1_rest, ps2_rest = remove p1 ps1, remove p2 ps2 in
    ps_cmp_total ps1_rest ps2_rest

assume Ps_cmp_is_total_order: total_order prins ps_cmp

val insert: prin -> eprins -> Tot prins
let insert p ps = union (singleton p) ps

val all_prins: unit -> Tot prins
let all_prins _ =
  insert Alice (insert Bob (insert Charlie (insert Dave (insert Evelyn (insert Fred empty)))))

val all_prins_superset_lemma:
  unit -> Lemma (requires (True)) (ensures (forall ps. subset ps (all_prins ())))
let all_prins_superset_lemma _ = ()

