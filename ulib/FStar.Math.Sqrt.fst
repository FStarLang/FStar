module FStar.Math.Sqrt

open FStar.Real
module ID = FStar.IndefiniteDescription

(* Square roots used to be the sole mathematical axiom of this module:

     assume val sqrt0 (x : rnonneg) : y:rnonneg{y *. y == x}

   They are now constructed, as

     sqrt x  =  lub { y | 0 <= y  /\  y * y <= x }

   using nothing but the completeness of [FStar.Real] ([FStar.Real.lub]).
   Z3's theory of reals is a theory of ordered *fields*, so it proves nothing
   that needs completeness and in particular gives no square roots; [lub] is a
   theorem of the Dedekind-cut construction that implements [FStar.Real] (see
   [FStar.Real.Dedekind]).

   The ordered-field algebra below is left to Z3. The only steps that need
   help are the nonlinear ones, which are hoisted into their own lemmas: in
   the middle of the main arguments the SMT context is large enough that they
   time out. *)

#set-options "--fuel 0 --ifuel 0 --z3rlimit 20"

(**** The set whose supremum is the square root *)

let sqrt_setp (x y:real) : prop = y >=. 0.0R /\ y *. y <=. x

let sqrt_set (x:real) : rset = sqrt_setp x

let sqrt_set_nonempty (x:real)
  : Lemma (requires x >=. 0.0R) (ensures is_nonempty (sqrt_set x))
  = introduce exists (y:real). sqrt_set x y with 0.0R and ()

/// Anything in [sqrt_set x] is at most [1 + x]: if [y] exceeded [1 + x] it
/// would exceed [1], so [y * y > y > x].
let sqrt_bound_aux (x y:real)
  : Lemma (requires x >=. 0.0R /\ sqrt_set x y) (ensures y <=. 1.0R +. x)
  = introduce 1.0R +. x <. y ==> False
    with begin
      assert (1.0R <. y);
      assert (y *. y >. y *. 1.0R)
    end

let sqrt_set_bounded (x:real)
  : Lemma (requires x >=. 0.0R) (ensures is_bounded_above (sqrt_set x))
  = introduce forall (y:real). sqrt_set x y ==> y <=. 1.0R +. x
    with introduce _ ==> _ with sqrt_bound_aux x y;
    introduce exists (b:real). is_upper_bound (sqrt_set x) b with (1.0R +. x) and ()

(**** The square root *)

#push-options "--ifuel 1"
let sqrt_tot (x:real) : real =
  if ID.strong_excluded_middle (x >=. 0.0R)
  then begin
    sqrt_set_nonempty x;
    sqrt_set_bounded x;
    lub (sqrt_set x)
  end
  else 0.0R

let sqrt_is_lub (x:real)
  : Lemma (requires x >=. 0.0R) (ensures is_lub (sqrt_set x) (sqrt_tot x))
  = sqrt_set_nonempty x; sqrt_set_bounded x

let sqrt_tot_neg (x:real)
  : Lemma (requires x <. 0.0R) (ensures sqrt_tot x == 0.0R)
  = ()
#pop-options

let sqrt_tot_nonneg (x:real)
  : Lemma (sqrt_tot x >=. 0.0R)
          [SMTPat (sqrt_tot x)]
  = introduce x >=. 0.0R ==> sqrt_tot x >=. 0.0R
    with begin
      sqrt_is_lub x;
      sqrt_set_nonempty x;
      assert (sqrt_set x 0.0R)
    end;
    introduce x <. 0.0R ==> sqrt_tot x >=. 0.0R with sqrt_tot_neg x

(**** The two analytic steps

   Both are stated without mentioning [sqrt_tot] or [lub]: keeping the
   least-upper-bound hypothesis out of the SMT context is worth orders of
   magnitude in verification time. *)

/// Some [e] with [0 < e <= a] and [e < b].
let small_pos2 (a b:real)
  : Ghost real (requires a >. 0.0R /\ b >. 0.0R)
               (ensures fun e -> e >. 0.0R /\ e <=. a /\ e <. b)
  = if a <. b then a else b /. two

/// From [e < d/w] and [w > 0], conclude [e * w < d].
let small_mul (e d w:real)
  : Lemma (requires w >. 0.0R /\ e <. d /. w) (ensures e *. w <. d)
  = assert (e *. w <. (d /. w) *. w);
    assert ((d /. w) *. w == d)

/// If [s^2 < x] then some [y > s] is still in [sqrt_set x]: take [y = s + e]
/// with [e] positive, at most [1], and below [(x - s^2)/(2s+1)]; then
/// [y^2 <= s^2 + e(2s+1) < x].
let sqrt_step_lt (x s:real)
  : Lemma (requires x >=. 0.0R /\ s >=. 0.0R /\ s *. s <. x)
          (ensures exists (y:real). y >=. 0.0R /\ y *. y <=. x /\ s <. y)
  = let d = x -. s *. s in
    let w = two *. s +. 1.0R in
    assert (w >. 0.0R);
    assert (d /. w >. 0.0R);
    let e = small_pos2 1.0R (d /. w) in
    small_mul e d w;
    let y = s +. e in
    assert (e *. e <=. e *. 1.0R);
    assert (y *. y == s *. s +. (two *. s *. e +. e *. e));
    assert (e *. w == two *. s *. e +. e);
    assert (y *. y <=. s *. s +. e *. w);
    introduce exists (y:real). y >=. 0.0R /\ y *. y <=. x /\ s <. y
    with y and ()

/// If [s^2 > x] then some [b < s] is still an upper bound of [sqrt_set x]:
/// take [b = s - e] with [e] positive, below [s], and below [(s^2 - x)/(2s)];
/// then [b^2 >= s^2 - 2se > x], so every member of the set is below [b].
let sqrt_step_gt (x s:real)
  : Lemma (requires x >=. 0.0R /\ s >=. 0.0R /\ x <. s *. s)
          (ensures exists (b:real).
                     b <. s /\
                     (forall (y:real). (y >=. 0.0R /\ y *. y <=. x) ==> y <=. b))
  = assert (s >. 0.0R);
    let d = s *. s -. x in
    let w = two *. s in
    assert (w >. 0.0R);
    assert (d /. w >. 0.0R);
    let e = small_pos2 s (d /. w) in
    small_mul e d w;
    let b = s -. e in
    assert (b >=. 0.0R);
    assert (e *. w == two *. s *. e);
    assert (b *. b == s *. s -. two *. s *. e +. e *. e);
    assert (b *. b >. x);
    introduce forall (y:real). (y >=. 0.0R /\ y *. y <=. x) ==> y <=. b
    with introduce (y >=. 0.0R /\ y *. y <=. x) ==> y <=. b with begin
      introduce b <. y ==> False
      with assert (y *. y >. b *. b)
    end;
    introduce exists (b:real).
                b <. s /\
                (forall (y:real). (y >=. 0.0R /\ y *. y <=. x) ==> y <=. b)
    with b and ()

(**** [sqrt_tot x] is neither too small nor too big *)

let sqrt_not_lt (x:real)
  : Lemma (requires x >=. 0.0R) (ensures ~(sqrt_tot x *. sqrt_tot x <. x))
  = sqrt_tot_nonneg x;
    sqrt_is_lub x;
    introduce sqrt_tot x *. sqrt_tot x <. x ==> False
    with begin
      sqrt_step_lt x (sqrt_tot x);
      eliminate exists (y:real). y >=. 0.0R /\ y *. y <=. x /\ sqrt_tot x <. y
      with assert (sqrt_set x y)
    end

let sqrt_not_gt (x:real)
  : Lemma (requires x >=. 0.0R) (ensures ~(x <. sqrt_tot x *. sqrt_tot x))
  = sqrt_tot_nonneg x;
    sqrt_is_lub x;
    introduce x <. sqrt_tot x *. sqrt_tot x ==> False
    with begin
      sqrt_step_gt x (sqrt_tot x);
      eliminate exists (b:real).
                  b <. sqrt_tot x /\
                  (forall (y:real). (y >=. 0.0R /\ y *. y <=. x) ==> y <=. b)
      with begin
        introduce forall (y:real). sqrt_set x y ==> y <=. b
        with introduce sqrt_set x y ==> y <=. b with assert (sqrt_setp x y);
        assert (is_upper_bound (sqrt_set x) b)
      end
    end

(**** The defining property *)

/// Hoisted: concluding [a == b] from the two negations is trivial, but doing
/// it in the ambient context of this module is not.
let trichotomy (a b:real)
  : Lemma (requires ~(a <. b) /\ ~(b <. a)) (ensures a == b)
  = ()

let sqrt_tot_square (x:real)
  : Lemma (requires x >=. 0.0R) (ensures sqrt_tot x *. sqrt_tot x == x)
  = sqrt_not_lt x;
    sqrt_not_gt x;
    trichotomy (sqrt_tot x *. sqrt_tot x) x

(**** The interface *)

let sqrt0 (x : rnonneg) : y:rnonneg{y *. y == x} =
  sqrt_tot_nonneg x;
  sqrt_tot_square x;
  sqrt_tot x

let sqrt = sqrt0

(* All of the proofs below work via SMT only. The lemma calls
   are just in case. *)

let sqrt_square (x : rnonneg)
  : Lemma (ensures sqrt x *. sqrt x == x)
          [SMTPat (sqrt x *. sqrt x)]
  = ()

let sqrt_unique (x : rnonneg) (y : rnonneg)
  : Lemma (requires y *. y == x)
          (ensures sqrt x == y)
  = ()

let sqrt_zero ()
  : Lemma (sqrt 0.0R == 0.0R)
  = sqrt_unique 0.0R 0.0R

let sqrt_one ()
  : Lemma (sqrt 1.0R == 1.0R)
  = sqrt_unique 1.0R 1.0R

let sqrt_sq (x : rnonneg)
  : Lemma (ensures sqrt (x *. x) == x)
  = sqrt_unique (x *. x) x

let sqrt_positive (x : rpos)
  : Lemma (ensures sqrt x >. 0.0R)
          [SMTPat (sqrt x)]
  = sqrt_square x

/// Squaring is monotone on the nonnegatives. Hoisted out of [sqrt_mono]:
/// this nonlinear step times out if left in a larger context.
let sq_le (a b:real)
  : Lemma (requires a >=. 0.0R /\ a <=. b) (ensures a *. a <=. b *. b)
  = assert (a *. a <=. a *. b)

let sqrt_mono (x y : rnonneg)
  : Lemma (requires x <. y) (ensures sqrt x <. sqrt y)
  = introduce sqrt y <=. sqrt x ==> False with sq_le (sqrt y) (sqrt x)

/// Hoisted for the same reason as [sq_le].
let mul4 (a b:real) : Lemma ((a *. b) *. (a *. b) == (a *. a) *. (b *. b)) = ()

let div4 (a b:real)
  : Lemma (requires b =!= 0.0R)
          (ensures b *. b =!= 0.0R /\
                   (a /. b) *. (a /. b) == (a *. a) /. (b *. b))
  = assert (b *. b =!= 0.0R);
    assert ((a /. b) *. (a /. b) *. (b *. b) == a *. a)

let sqrt_mul (x y : rnonneg)
  : Lemma (ensures sqrt (x *. y) == sqrt x *. sqrt y)
  = sqrt_square x;
    sqrt_square y;
    mul4 (sqrt x) (sqrt y);
    sqrt_unique (x *. y) (sqrt x *. sqrt y)

let sqrt_div (x : rnonneg) (y : rpos)
  : Lemma (ensures sqrt (x /. y) == sqrt x /. sqrt y)
  = sqrt_square x;
    sqrt_square y;
    sqrt_positive y;
    div4 (sqrt x) (sqrt y);
    sqrt_unique (x /. y) (sqrt x /. sqrt y)
