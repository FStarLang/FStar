module BugLexTop
(*
   This is a bug report due to Son Ho,
   Also, with contributions from Jay Bosamiya for the proof of False.
   It was fixed in 92e50f9b5ba34afe97b2cc09ba66dfa090438825
*)
val n_lexcons : nat -> lex_t
let rec n_lexcons n =
  if n = 0 then LexTop else LexCons LexTop (n_lexcons (n-1))

/// Previously, this used to go through, because we had `LexCons _ _ << LexTop`
[@(expect_failure [19])]
let rec decrease_lexcons (n:nat)
 : Lemma (n_lexcons (n+1) << n_lexcons n)
 = if n = 0 then () else decrease_lexcons (n-1)

/// Letting it go through quickly leads to a proof of false, as shown below
/// by Son and Jay
assume
val decrease_lexcons_bad : n:nat -> Lemma (n_lexcons (n+1) << n_lexcons n)

val infinite_fun : n:nat -> x:lex_t{x==n_lexcons n} -> Tot False (decreases x)
let rec infinite_fun n x =
  decrease_lexcons_bad n;
  infinite_fun (n+1) (n_lexcons (n+1))

/// You can no longer meaningfully relate lex tuples of different length
[@(expect_failure [19])]
let rec f (x:nat) (y:nat)
  : Tot nat
    (decreases (LexCons x LexTop))
  = if y > 0
    then g x (y - 1)
    else if x > 0
    then f (x - 1) y
    else x
and g (x:nat) (y:nat)
  : Tot nat
    (decreases (LexCons x (LexCons y LexTop)))
  = if x = 0 then 0
    else f (x - 1) (x + 1)


/// You must "pad" out the lex tuples to the same length to relate
/// them by <<
let rec h (x:nat) (y:nat)
  : Tot nat
    (decreases (LexCons x (LexCons y LexTop)))
  = if y > 0
    then i x (y - 1)
    else if x > 0
    then h (x - 1) y
    else x
and i (x:nat) (y:nat)
  : Tot nat
    (decreases (LexCons x (LexCons y LexTop)))
  = if x = 0 then 0
    else h (x - 1) (x + 1)
