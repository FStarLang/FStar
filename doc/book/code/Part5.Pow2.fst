module Part5.Pow2

(* Now (2025/7/16), the pow2_values lemma is in FStar.Math.Lemmas, which
we mention and therefore depend on. We therefore get some facts
about pow2 that break this example (break = make more things work than they should). So,
ignore these facts here to retain the example. What we would really want
though is a way to scope SMT patterns. *)
#set-options "--using_facts_from -FStar.Math.Lemmas"

[@@expect_failure [19]]
//SNIPPET_START: pow2_0
let pow2_bound_19 (x:nat{x <= 19}) : Lemma (pow2 x < 1000000) =
  assert (forall (x y : nat). x <= y ==> pow2 x <= pow2 y);
  assert (pow2 19 ==  524288);
  assert (pow2 x < 1000000);
  ()
//SNIPPET_END: pow2_0

[@@expect_failure [19]]
//SNIPPET_START: pow2_1
let pow2_bound_19' (x:nat{x <= 19}) : Lemma (pow2 x < 1000000) =
  FStar.Math.Lemmas.pow2_le_compat 19 x;
  assert (pow2 19 == 524288);
  assert (pow2 x < 1000000);
  ()
//SNIPPET_END: pow2_1

open FStar.Tactics

//SNIPPET_START: pow2_2
let pow2_bound_19'' (x:nat{x <= 19}) : Lemma (pow2 x < 1000000) =
  FStar.Math.Lemmas.pow2_le_compat 19 x;
  assert (pow2 19 == 524288) by compute ();
  assert (pow2 x < 1000000);
  ()
//SNIPPET_END: pow2_2

//SNIPPET_START: pow2_3
let pow2_bound_19''' (x:nat{x <= 19}) : Lemma (pow2 x < 1000000) =
  FStar.Math.Lemmas.pow2_le_compat 19 x;
  assert (pow2 19 == 524288) by (compute (); dump "after compute");
  assert (pow2 x < 1000000);
  ()
//SNIPPET_END: pow2_3

//SNIPPET_START: pow2_4
let pow2_bound_19'''' (x:nat{x <= 19}) : Lemma (pow2 x < 1000000) =
  FStar.Math.Lemmas.pow2_le_compat 19 x;
  assert (pow2 19 == 524288) by (
    compute ();
    trivial ();
    qed ()
   );
  assert (pow2 x < 1000000);
  ()
//SNIPPET_END: pow2_4
