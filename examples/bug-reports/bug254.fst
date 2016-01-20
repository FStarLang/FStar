(*--build-config
    other-files:FStar.List.fst
--*)

module Bug254
open List

val foo : list nat -> Tot bool
let foo _ = true

val bar : ms1:list (nat * nat)
        -> ms2:list (nat * nat){mapT #_ #nat fst ms1 = mapT #_ #nat fst ms2}
        -> Lemma
        (requires (foo (mapT fst ms1)))
        (ensures true)
let bar ms1 ms2 =
let x = mapT fst ms1 in
let y = mapT fst ms2 in
(** this fails, but removing any one of the assertions below succeeds *)
let _ = assert (foo x) in
let _ = assert (x = y) in
()
