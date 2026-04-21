module Bug3175

open FStar.Tactics.V2

#set-options "--admit_smt_queries true"

[@@expect_failure]
let aux2 (p:Type0)
: Lemma True
= calc (==>) {
    squash p;
    ==> { _ by (hyp (nth_var (-1))) }
    p;
  }
