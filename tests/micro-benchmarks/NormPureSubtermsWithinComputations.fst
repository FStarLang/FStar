module NormPureSubtermsWithinComputations
open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST
open FStar.List.Tot
open FStar.Tactics

#set-options "--fuel 0 --ifuel 0 --z3rlimit 15"
let pp1 () : Tac unit =
  norm [primops; iota; delta_only [`%List.Tot.Base.length]; zeta];
  dump "after norm";
  trefl ()

// This one reduces to 3
[@@ Tactics.postprocess_with pp1]
let f1 () : Stack nat (requires (fun _ -> True)) (ensures (fun _ _ _-> True)) =
  length [0; 1; 2]

let pp2 () : Tac unit =
  norm [primops; iota; delta_only [`%List.Tot.Base.length]; zeta_full;
  delta_qualifier [
    "pure_subterms_within_computations"
  ];
  ];
  dump "after norm";
  trefl ()

[@@ Tactics.postprocess_with pp2]
let f2 (x:unit) : Stack nat (requires (fun _ -> True)) (ensures (fun _ _ _-> True)) =
  length [0; 1; 2]

let f3 (x:unit) : Stack nat (requires (fun _ -> True)) (ensures (fun _ _ _-> True)) =
  3

let test_f2_f3 () =
  assert (f2 == f3)
    by (dump "A"; trefl(); qed())

assume
val f (x:int) : St int

[@@postprocess_with
   (fun _ -> norm [delta_qualifier ["pure_subterms_within_computations"]];
          trefl())]
let test_inline_let (x:int) : St int =
  [@inline_let]
  let y = x + 1 in
  let z = f (y + 1) in
  f (z + z)

let test_inline_let_expeted (x:int) : St int =
  let z = f ((x + 1) + 1) in
  f (z + z)

let check_inline_let () =
  assert (test_inline_let == test_inline_let_expeted)
    by (trefl(); qed())
