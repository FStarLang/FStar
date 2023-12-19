module Bug3175

open FStar.Tactics.V2

#set-options "--lax"

[@@expect_failure [217]]
let aux2 (p:Type0)
: Lemma True
= calc (==>) {
    squash p;
    ==> { _ by (apply (`Squash.join_squash); hyp (nth_var (-1))) }
    p;
  }
