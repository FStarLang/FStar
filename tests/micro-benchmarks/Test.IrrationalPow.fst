module Test.IrrationalPow

open FStar.Real
module P = FStar.Math.Pow
module S = FStar.Math.Sqrt

#set-options "--fuel 1 --ifuel 0 --z3rlimit 10"

let is_rational (x:real) : prop =
  exists (m:int) (n:pos). x == of_int m /. of_int n

let is_irrational (x:real) : prop = ~ (is_rational x)

assume val sqrt_two_irrational : unit -> Lemma (is_irrational (S.sqrt 2.0R))

/// Dov Jarden, Curiosa No. 339, Scripta Mathematica 19 (1953), p. 229.
/// Case analysis on whether sqrt(2)^sqrt(2) is rational.
/// https://queuea9.wordpress.com/2015/01/27/the-square-root-of-two-proof/
let irrational_pow_rational ()
  : Lemma (exists (a b:P.rpos).
      is_irrational a /\ is_irrational b /\ is_rational (P.pow a b))
  = let s = S.sqrt 2.0R in
    S.sqrt_positive 2.0R;
    sqrt_two_irrational ();
    let t = P.pow s s in
    if is_rational t then
      introduce exists (a b:P.rpos).
        is_irrational a /\ is_irrational b /\ is_rational (P.pow a b)
      with s s and ()
    else begin
      S.sqrt_square 2.0R;
      P.pow_pow s s s;
      P.pow_one s;
      P.pow_succ s 1;
      assert (P.pow t s == 2.0R);
      introduce exists (m:int) (n:pos). P.pow t s == of_int m /. of_int n
      with 2 1 and ();
      introduce exists (a b:P.rpos).
        is_irrational a /\ is_irrational b /\ is_rational (P.pow a b)
      with t s and ()
    end
