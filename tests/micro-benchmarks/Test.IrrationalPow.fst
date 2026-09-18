module Test.IrrationalPow

open FStar.Real
module P = FStar.Math.Pow
module S = FStar.Math.Sqrt

#set-options "--fuel 1 --ifuel 0 --z3rlimit 10"

let is_rational (x:real) : prop =
  exists (m:int) (n:pos). x == of_int m /. of_int n

let is_irrational (x:real) : prop = ~ (is_rational x)

let square_difference (a b:int)
  : Lemma ((a-b)*(a-b) == a*a - 2*a*b + b*b) = ()

let square_product (a b:real)
  : Lemma ((a *. b) *. (a *. b) == (a *. a) *. (b *. b)) = ()

/// From m^2 = 2*n^2, descend to (2*n-m)^2 = 2*(m-n)^2.
/// The new denominator m-n is positive and smaller than n.
let rec sqrt_two_descent (m n:pos)
  : Lemma (requires m*m == 2*n*n) (ensures False) (decreases n)
  = assert (n < m /\ m < 2*n);
    square_difference (2*n) m;
    square_difference m n;
    sqrt_two_descent (2*n-m) (m-n)

let sqrt_two_irrational () : Lemma (is_irrational (S.sqrt 2.0R))
  = S.sqrt_positive 2.0R;
    S.sqrt_square 2.0R;
    introduce is_rational (S.sqrt 2.0R) ==> False with begin
      eliminate exists (m:int) (n:pos).
        S.sqrt 2.0R == of_int m /. of_int n
      with begin
        assert (of_int m == S.sqrt 2.0R *. of_int n);
        assert (m > 0);
        square_product (S.sqrt 2.0R) (of_int n);
        assert (of_int (m*m) == of_int (2*n*n));
        assert (m*m == 2*n*n);
        sqrt_two_descent m n
      end
    end

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
