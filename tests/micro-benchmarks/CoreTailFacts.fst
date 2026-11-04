module CoreTailFacts

(* The facts established by the last lemma of each branch of an [if] whose
   type, [unit], was pushed into its branches reach the rest of the
   computation. *)
assume val p : int -> prop
assume val q : int -> prop
assume val lemma0 (x:int) : Lemma True
assume val lemma_p (x:int) : Lemma (p x)
assume val lemma_q (x:int) : Lemma (q x)

#push-options "--fuel 0 --ifuel 0"
let test (x:int) : Tot (u:unit{x >= 0 ==> p x}) =
  if x >= 0 then (lemma0 x; lemma_p x)
  else (lemma0 x; lemma_q x);
  ()

let test_let (x:int) : squash (p x /\ q x) =
  let _ : unit = (lemma0 x; lemma_p x) in
  let _ : unit = if x > 0 then (lemma0 x; lemma_q x) else (lemma0 x; lemma_q x) in
  ()
#pop-options
