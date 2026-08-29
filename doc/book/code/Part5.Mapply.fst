module Part5.Mapply

open FStar.Tactics

//SNIPPET_START: mapply
assume val p : prop
assume val q : prop
assume val r : prop
assume val s : prop

assume val p_q : unit -> Lemma (requires p) (ensures q)
assume val p_r : squash p -> Lemma r
assume val qr_s : unit -> Lemma (q ==> r ==> s)

let test () : Lemma (requires p) (ensures s) =
  assert s by (
    mapply (`qr_s);
    mapply (`p_q);
    mapply (`p_r);
    ()
  )
//SNIPPET_END: mapply
