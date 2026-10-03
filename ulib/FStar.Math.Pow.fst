module FStar.Math.Pow

open FStar.Real
module ID = FStar.IndefiniteDescription

(* Construct real exponentiation from least upper bounds.

   For a >= 1 and x >= 0, pow a x is the supremum of power_set a x.
   The set contains 1. If x <= k, every member y satisfies y <= a^k:
   from y^n <= a^m and m <= k*n, compare nth powers.

   For rational x=m/n, the supremum is the unique positive nth root of a^m.
   Existence of this root is proved below from lub and an elementary bound
   on differences of natural powers. Finally reciprocals handle negative
   exponents and positive bases below 1.

   Least upper bounds and the Archimedean property come from FStar.Real.
   Classical sign decisions use erased choice from FStar.IndefiniteDescription. *)

#set-options "--fuel 1 --ifuel 0 --z3rlimit 20"

let scale_le (x y c:real)
  : Lemma (requires x <=. y /\ 0.0R <=. c) (ensures x *. c <=. y *. c) = ()

/// Natural powers used in the bounds defining real exponentiation.
let rec pow_nat (a:real) (n:nat)
  : Tot (r:real{(a >=. 0.0R ==> r >=. 0.0R) /\ (a >. 0.0R ==> r >. 0.0R)})
      (decreases n) =
  if n = 0 then 1.0R else a *. pow_nat a (n - 1)

let pow_nat_zero (a:real) : Lemma (pow_nat a 0 == 1.0R) = ()
let pow_nat_succ (a:real) (n:nat)
  : Lemma (pow_nat a (n+1) == a *. pow_nat a n) = ()

#push-options "--fuel 2"
let nat_first (a:real) : Lemma (pow_nat a 1 == a) = ()
#pop-options

let nat_nonneg (a:real) (n:nat)
  : Lemma (requires a >=. 0.0R) (ensures pow_nat a n >=. 0.0R) = ()

let nat_pos (a:real) (n:nat)
  : Lemma (requires a >. 0.0R) (ensures pow_nat a n >. 0.0R) = ()

let rec nat_one (n:nat) : Lemma (pow_nat 1.0R n == 1.0R) (decreases n)
  = if n > 0 then nat_one (n - 1)

let rec nat_add (a:real) (m n:nat)
  : Lemma (pow_nat a (m+n) == pow_nat a m *. pow_nat a n) (decreases m)
  = if m > 0 then nat_add a (m-1) n

let rec nat_mul (a:real) (m n:nat)
  : Lemma (pow_nat a (m*n) == pow_nat (pow_nat a m) n) (decreases n)
  = if n > 0 then (nat_mul a m (n-1); nat_add a m (m*(n-1)))

let mul_assoc (a b c:real) : Lemma ((a *. b) *. c == a *. (b *. c)) = ()

let mul_reorder (a b c d:real)
  : Lemma ((a *. b) *. (c *. d) == (a *. c) *. (b *. d))
  = mul_assoc a b (c *. d);
    mul_assoc b c d;
    mul_assoc c b d;
    mul_assoc a c (b *. d)

let rec nat_product (a b:real) (n:nat)
  : Lemma (pow_nat (a *. b) n == pow_nat a n *. pow_nat b n) (decreases n)
  = if n > 0 then begin
      nat_product a b (n-1);
      mul_reorder a b (pow_nat a (n-1)) (pow_nat b (n-1))
    end

let rec nat_mono (a b:real) (n:nat)
  : Lemma (requires 0.0R <=. a /\ a <=. b)
          (ensures pow_nat a n <=. pow_nat b n) (decreases n)
  = if n > 0 then begin
      nat_mono a b (n-1);
      nat_nonneg a (n-1);
      nat_nonneg b (n-1);
      assert (a *. pow_nat a (n-1) <=. b *. pow_nat a (n-1))
    end

let rec nat_strict (a b:real) (n:pos)
  : Lemma (requires 0.0R <=. a /\ a <. b)
          (ensures pow_nat a n <. pow_nat b n) (decreases n)
  = if n > 1 then begin
      nat_strict a b (n-1);
      nat_nonneg a (n-1);
      nat_pos b (n-1);
      assert (a *. pow_nat a (n-1) <=. a *. pow_nat b (n-1));
      assert (a *. pow_nat b (n-1) <. b *. pow_nat b (n-1))
    end
    else (nat_first a; nat_first b)

let nat_reflect (a b:real) (n:pos)
  : Lemma (requires 0.0R <=. a /\ 0.0R <=. b /\ pow_nat a n <=. pow_nat b n)
          (ensures a <=. b)
  = introduce b <. a ==> False with nat_strict b a n

let nat_ge_one (a:real) (n:nat)
  : Lemma (requires a >=. 1.0R) (ensures pow_nat a n >=. 1.0R)
  = nat_one n; nat_mono 1.0R a n

let nat_exp_mono (a:real) (m n:nat)
  : Lemma (requires a >=. 1.0R /\ m <= n)
          (ensures pow_nat a m <=. pow_nat a n)
  = nat_ge_one a m; nat_ge_one a (n-m); nat_add a m (n-m)

/// For a >= 1 and x >= 0, take lower bounds of rational powers a^(m/n)
/// with m/n <= x. Natural-power inequalities avoid choosing roots here.
let power_set (a x y:real) : prop =
  y >=. 0.0R /\
  (exists (m:nat) (n:pos).
    of_int m <=. x *. of_int n /\ pow_nat y n <=. pow_nat a m)

/// The defining set contains 1.
let power_set_one (a x:real)
  : Lemma (requires a >=. 1.0R /\ x >=. 0.0R)
          (ensures power_set a x 1.0R)
  = nat_first 1.0R;
    introduce exists (m:nat) (n:pos).
      of_int m <=. x *. of_int n /\ pow_nat 1.0R n <=. pow_nat a m
    with 0 1 and ()

let power_set_bound (a x y:real) (k:nat)
  : Lemma (requires a >=. 1.0R /\ x <=. of_int k /\ power_set a x y)
          (ensures y <=. pow_nat a k)
  = eliminate exists (m:nat) (n:pos).
      of_int m <=. x *. of_int n /\ pow_nat y n <=. pow_nat a m
    with begin
      assert (of_int m <=. of_int k *. of_int n);
      assert (m <= k*n);
      nat_exp_mono a m (k*n);
      nat_mul a k n;
      nat_ge_one a k;
      nat_reflect y (pow_nat a k) n
    end

let power_set_ready (a x:real)
  : Lemma (requires a >=. 1.0R /\ x >=. 0.0R)
          (ensures is_nonempty (power_set a x) /\ is_bounded_above (power_set a x))
  = power_set_one a x;
    introduce exists (y:real). power_set a x y with 1.0R and ();
    archimedean x;
    eliminate exists (k:nat). x <. of_int k
    with begin
      introduce forall (y:real). power_set a x y ==> y <=. pow_nat a k
      with introduce _ ==> _ with power_set_bound a x y k;
      introduce exists (b:real). is_upper_bound (power_set a x) b
      with (pow_nat a k) and ()
    end

// Keep the quantified supremum property out of arithmetic goals.
// Use power_lub to make it available to the solver when needed.
[@@"opaque_to_smt"]
let power_ge_one (a:real{a >=. 1.0R}) (x:real{x >=. 0.0R})
  : Tot (r:real{r >=. 1.0R})
  = power_set_ready a x;
    power_set_one a x;
    lub (power_set a x)

let power_lub (a:real{a >=. 1.0R}) (x:real{x >=. 0.0R})
  : Lemma (is_lub (power_set a x) (power_ge_one a x))
  = reveal_opaque (`%power_ge_one) power_ge_one;
    power_set_ready a x; power_set_one a x

let power_nat (a:real{a >=. 1.0R}) (k:nat)
  : Lemma (power_ge_one a (of_int k) == pow_nat a k)
  = nat_ge_one a k;
    nat_first (pow_nat a k);
    introduce exists (m:nat) (n:pos).
      of_int m <=. of_int k *. of_int n /\ pow_nat (pow_nat a k) n <=. pow_nat a m
    with k 1 and ();
    assert (power_set a (of_int k) (pow_nat a k));
    power_lub a (of_int k);
    introduce forall (y:real). power_set a (of_int k) y ==> y <=. pow_nat a k
    with introduce _ ==> _ with power_set_bound a (of_int k) y k;
    assert (is_upper_bound (power_set a (of_int k)) (pow_nat a k))

let power_mono (a:real{a >=. 1.0R}) (x y:real{0.0R <=. x /\ x <=. y})
  : Lemma (power_ge_one a x <=. power_ge_one a y)
  = power_lub a x; power_lub a y;
    introduce forall (z:real). power_set a x z ==> power_set a y z
    with introduce power_set a x z ==> power_set a y z with begin
      eliminate exists (m:nat) (n:pos).
        of_int m <=. x *. of_int n /\ pow_nat z n <=. pow_nat a m
      with begin
        scale_le x y (of_int n);
        introduce exists (m':nat) (n':pos).
        of_int m' <=. y *. of_int n' /\ pow_nat z n' <=. pow_nat a m'
        with m n and ()
      end
    end;
    assert (is_upper_bound (power_set a x) (power_ge_one a y))

let ratio_cancel (m:nat) (n:pos)
  : Lemma ((of_int m /. of_int n) *. of_int n == of_int m) = ()

let ratio_cross (k m:nat) (l n:pos)
  : Lemma (requires of_int k <=. (of_int m /. of_int n) *. of_int l)
          (ensures k*n <= m*l /\ k*n >= 0 /\ m*l >= 0 /\ l*n > 0)
  = assert (of_int k *. of_int n <=. of_int m *. of_int l)

let power_rational_bound (a:real{a >=. 1.0R}) (m:nat) (n:pos)
  (r:real{r >=. 0.0R /\ pow_nat r n == pow_nat a m}) (y:real)
  : Lemma (requires power_set a (of_int m /. of_int n) y) (ensures y <=. r)
  = eliminate exists (k:nat) (l:pos).
      of_int k <=. (of_int m /. of_int n) *. of_int l /\ pow_nat y l <=. pow_nat a k
    with begin
      ratio_cross k m l n;
      nat_nonneg y l;
      nat_mono (pow_nat y l) (pow_nat a k) n;
      nat_mul y l n;
      nat_mul a k n;
      nat_exp_mono a (k*n) (m*l);
      nat_mul a m l;
      nat_mul r n l;
      nat_reflect y r (l*n)
    end

/// Identify the supremum with any candidate having the expected rational power.
let power_rational_unique (a:real{a >=. 1.0R}) (m:nat) (n:pos)
  (r:real{r >=. 0.0R /\ pow_nat r n == pow_nat a m})
  : Lemma (power_ge_one a (of_int m /. of_int n) == r)
  = let x = of_int m /. of_int n in
    ratio_cancel m n;
    introduce exists (k:nat) (l:pos).
      of_int k <=. x *. of_int l /\ pow_nat r l <=. pow_nat a k
    with m n and ();
    assert (power_set a x r);
    introduce forall (y:real). power_set a x y ==> y <=. r
    with introduce _ ==> _ with power_rational_bound a m n r y;
    power_lub a x;
    assert (is_upper_bound (power_set a x) r)

/// A Lipschitz constant for the nth power on [0,m], where m >= 1.
/// The recurrence supports the inductive proof in nat_lipschitz.
let rec slope (m:real) (n:nat) : Tot real (decreases n) =
  if n = 0 then 0.0R else pow_nat m (n-1) +. m *. slope m (n-1)

let rec slope_nonneg (m:real{m >=. 1.0R}) (n:nat)
  : Lemma (slope m n >=. 0.0R) (decreases n)
  = if n > 0 then (slope_nonneg m (n-1); nat_ge_one m (n-1))

let slope_pos (m:real{m >=. 1.0R}) (n:pos)
  : Lemma (slope m n >. 0.0R)
  = slope_nonneg m (n-1); nat_ge_one m (n-1)

let difference_step (u v p q c d m:real)
  : Lemma (requires 0.0R <=. u /\ u <=. v /\ v <=. m /\
                    0.0R <=. c /\ 0.0R <=. d /\ p <=. d /\
                    q -. p <=. (v -. u) *. c)
          (ensures v *. q -. u *. p <=. (v -. u) *. (d +. m *. c))
  = assert (v *. q -. u *. p == v *. (q -. p) +. (v -. u) *. p);
    assert (v *. (q -. p) <=. v *. ((v -. u) *. c));
    assert ((v -. u) *. p <=. (v -. u) *. d);
    assert (v *. ((v -. u) *. c) <=. m *. ((v -. u) *. c))

let rec nat_lipschitz (m u v:real) (n:nat)
  : Lemma (requires 1.0R <=. m /\ 0.0R <=. u /\ u <=. v /\ v <=. m)
          (ensures pow_nat v n -. pow_nat u n <=. (v -. u) *. slope m n)
          (decreases n)
  = if n > 0 then begin
      nat_lipschitz m u v (n-1);
      nat_mono u m (n-1);
      nat_ge_one m (n-1);
      slope_nonneg m (n-1);
      difference_step u v (pow_nat u (n-1)) (pow_nat v (n-1))
        (slope m (n-1)) (pow_nat m (n-1)) m
    end

let root_set (a:real) (n:pos) (r:real) : prop =
  r >=. 0.0R /\ pow_nat r n <=. a

let root_bound (a:real{a >=. 1.0R}) (n:pos) (r:real)
  : Lemma (requires root_set a n r) (ensures r <=. a +. 1.0R)
  = introduce a +. 1.0R <. r ==> False
    with begin
      nat_exp_mono r 1 n;
      nat_first r
    end

let root_ready (a:real{a >=. 1.0R}) (n:pos)
  : Lemma (is_nonempty (root_set a n) /\ is_bounded_above (root_set a n))
  = nat_one n;
    introduce exists (r:real). root_set a n r with 1.0R and ();
    introduce forall (r:real). root_set a n r ==> r <=. a +. 1.0R
    with introduce _ ==> _ with root_bound a n r;
    introduce exists (b:real). is_upper_bound (root_set a n) b
    with (a +. 1.0R) and ()

let small (s d c:real{0.0R <. s /\ 0.0R <. d /\ 0.0R <. c})
  : GTot (e:real{0.0R <. e /\ e <=. s /\ e *. c <. d})
  = let t = d /. (2.0R *. c) in
    if s <=. t then s else t

let root_step_up (a s:real) (n:pos)
  : Lemma (requires 1.0R <=. s /\ pow_nat s n <. a)
          (ensures exists (r:real). root_set a n r /\ s <. r)
  = let m = s +. 1.0R in
    slope_pos m n;
    let e = small 1.0R (a -. pow_nat s n) (slope m n) in
    nat_lipschitz m s (s +. e) n;
    introduce exists (r:real). root_set a n r /\ s <. r
    with (s +. e) and ()

let root_step_down (a s:real) (n:pos)
  : Lemma (requires 1.0R <=. s /\ a <. pow_nat s n)
          (ensures exists (b:real). b <. s /\ is_upper_bound (root_set a n) b)
  = let m = s +. 1.0R in
    slope_pos m n;
    let e = small s (pow_nat s n -. a) (slope m n) in
    let b = s -. e in
    nat_lipschitz m b s n;
    introduce forall (r:real). root_set a n r ==> r <=. b
    with introduce root_set a n r ==> r <=. b with begin
      introduce b <. r ==> False with nat_mono b r n
    end;
    introduce exists (b:real). b <. s /\ is_upper_bound (root_set a n) b
    with b and ()

let trichotomy (a b:real)
  : Lemma (requires ~(a <. b) /\ ~(b <. a)) (ensures a == b) = ()

/// The supremum of root_set a n is the positive nth root of a.
/// Used to establish the defining equation for nonnegative rational exponents.
let root (a:real{a >=. 1.0R}) (n:pos)
  : Tot (r:real{r >=. 1.0R /\ pow_nat r n == a})
  = root_ready a n;
    nat_one n;
    let s = lub (root_set a n) in
    assert (s >=. 1.0R);
    introduce pow_nat s n <. a ==> False
    with begin
      root_step_up a s n;
      eliminate exists (r:real). root_set a n r /\ s <. r with ()
    end;
    introduce a <. pow_nat s n ==> False
    with begin
      root_step_down a s n;
      eliminate exists (b:real). b <. s /\ is_upper_bound (root_set a n) b with ()
    end;
    trichotomy (pow_nat s n) a;
    s

let power_rational (a:real{a >=. 1.0R}) (m:nat) (n:pos)
  : Lemma (pow_nat (power_ge_one a (of_int m /. of_int n)) n == pow_nat a m)
  = nat_ge_one a m;
    let r = root (pow_nat a m) n in
    power_rational_unique a m n r

let power_base_one (x:real{x >=. 0.0R})
  : Lemma (power_ge_one 1.0R x == 1.0R)
  = power_lub 1.0R x;
    introduce forall (y:real). power_set 1.0R x y ==> y <=. 1.0R
    with introduce power_set 1.0R x y ==> y <=. 1.0R with begin
      eliminate exists (m:nat) (n:pos).
        of_int m <=. x *. of_int n /\ pow_nat y n <=. pow_nat 1.0R m
      with begin
        nat_one m; nat_one n;
        nat_reflect y 1.0R n
      end
    end;
    assert (is_upper_bound (power_set 1.0R x) 1.0R)

let nat_inverse (a:real{a >. 0.0R}) (n:nat)
  : Lemma (pow_nat (1.0R /. a) n == 1.0R /. pow_nat a n)
  = nat_pos a n;
    nat_product a (1.0R /. a) n;
    nat_one n

let reciprocal (a:real{a >. 0.0R}) : Tot (r:real{r >. 0.0R}) = 1.0R /. a

let reciprocal_laws (a:real{a >. 0.0R})
  : Lemma (1.0R /. (1.0R /. a) == a /\
           (a <. 1.0R ==> 1.0R /. a >. 1.0R) /\
           (a >. 1.0R ==> 1.0R /. a <. 1.0R)) = ()

let reciprocal_antitone (a b:real{0.0R <. a /\ a <=. b})
  : Lemma (1.0R /. b <=. 1.0R /. a) = ()

/// Positive bases admit every real exponent. For a < 1, invert the base;
/// for negative exponents, invert the result. Reals are erased, so these
/// classical sign tests do not extract to numerical code.
let pow (a:real{a >. 0.0R}) (x:real) : Tot (r:real{r >. 0.0R}) =
  if ID.strong_excluded_middle (a >=. 1.0R) then
    if ID.strong_excluded_middle (x >=. 0.0R)
    then power_ge_one a x
    else reciprocal (power_ge_one a (0.0R -. x))
  else
    if ID.strong_excluded_middle (x >=. 0.0R)
    then reciprocal (power_ge_one (1.0R /. a) x)
    else power_ge_one (1.0R /. a) (0.0R -. x)

let pow_positive (a:real{a >. 0.0R}) (x:real)
  : Lemma (pow a x >. 0.0R) = ()

let pow_zero (a:real{a >. 0.0R}) : Lemma (pow a 0.0R == 1.0R)
  = if a >=. 1.0R then power_nat a 0
    else power_nat (1.0R /. a) 0

let pow_one (a:real{a >. 0.0R}) : Lemma (pow a 1.0R == a)
  = if a >=. 1.0R then (power_nat a 1; nat_first a)
    else (power_nat (1.0R /. a) 1; nat_first (1.0R /. a))

let pow_one_base (x:real) : Lemma (pow 1.0R x == 1.0R)
  = if x >=. 0.0R then power_base_one x
    else power_base_one (0.0R -. x)

let pow_neg (a:real{a >. 0.0R}) (x:real)
  : Lemma (pow a (0.0R -. x) == 1.0R /. pow a x)
  = if x == 0.0R then pow_zero a

let pow_inverse_base (a:real{a >. 0.0R}) (x:real)
  : Lemma (pow (1.0R /. a) x == 1.0R /. pow a x)
  = reciprocal_laws a;
    if a == 1.0R then pow_one_base x
    else if a >. 1.0R then
      if x >=. 0.0R then ()
      else reciprocal_laws (power_ge_one a (0.0R -. x))
    else
      if x >=. 0.0R then reciprocal_laws (power_ge_one (1.0R /. a) x)
      else ()

let pow_of_nat (a:real{a >. 0.0R}) (n:nat)
  : Lemma (pow a (of_int n) == pow_nat a n)
  = if a >=. 1.0R then power_nat a n
    else begin
      power_nat (1.0R /. a) n;
      nat_inverse a n;
      reciprocal_laws (pow_nat a n)
    end

let pow_of_int (a:rpos) (n:int)
  : Lemma (pow a (of_int n) ==
      (if n >= 0 then pow_nat a n else 1.0R /. pow_nat a (-n)))
  = if n >= 0 then pow_of_nat a n
    else begin
      pow_of_nat a (-n);
      pow_neg a (of_int (-n))
    end

let pow_succ (a:rpos) (n:int)
  : Lemma (pow a (of_int (n+1)) == a *. pow a (of_int n))
  = pow_of_int a n;
    pow_of_int a (n+1);
    if n >= 0 then pow_nat_succ a n
    else if n = -1 then (pow_nat_zero a; nat_first a)
    else pow_nat_succ a (-n-1)

let pow_rational_nat (a:real{a >. 0.0R}) (m:nat) (n:pos)
  : Lemma (pow_nat (pow a (of_int m /. of_int n)) n == pow_nat a m)
  = if a >=. 1.0R then power_rational a m n
    else begin
      let b = 1.0R /. a in
      let x = of_int m /. of_int n in
      power_rational b m n;
      nat_inverse (power_ge_one b x) n;
      nat_inverse a m;
      reciprocal_laws (pow_nat a m)
    end

let pow_rational (a:rpos) (m:nat) (n:pos)
  : Lemma (pow (pow a (of_int m /. of_int n)) (of_int n) == pow a (of_int m))
  = pow_rational_nat a m n;
    pow_of_nat (pow a (of_int m /. of_int n)) n;
    pow_of_nat a m

let pow_rational_unique (a:rpos) (m:nat) (n:pos) (r:rpos)
  : Lemma (requires pow r (of_int n) == pow a (of_int m))
          (ensures pow a (of_int m /. of_int n) == r)
  = pow_of_nat r n;
    pow_of_nat a m;
    pow_rational_nat a m n;
    nat_reflect r (pow a (of_int m /. of_int n)) n;
    nat_reflect (pow a (of_int m /. of_int n)) r n

let pow_half (a:real{a >. 0.0R})
  : Lemma (pow a 0.5R == FStar.Math.Sqrt.sqrt a)
  = pow_rational_nat a 1 2;
    nat_first a;
    nat_first (pow a 0.5R);
    FStar.Math.Sqrt.sqrt_unique a (pow a 0.5R)

let pow_mono (a:real{a >=. 1.0R}) (x y:real{x <=. y})
  : Lemma (pow a x <=. pow a y)
  = if x >=. 0.0R then power_mono a x y
    else if y <=. 0.0R then begin
      power_mono a (0.0R -. y) (0.0R -. x);
      reciprocal_antitone (power_ge_one a (0.0R -. y)) (power_ge_one a (0.0R -. x));
      if y == 0.0R then (power_nat a 0; pow_zero a)
    end
    else reciprocal_antitone 1.0R (power_ge_one a (0.0R -. x))

let pow_antitone (a:real{0.0R <. a /\ a <=. 1.0R}) (x y:real{x <=. y})
  : Lemma (pow a y <=. pow a x)
  = let b = 1.0R /. a in
    pow_mono b x y;
    reciprocal_antitone (pow b x) (pow b y);
    pow_inverse_base b x;
    pow_inverse_base b y;
    reciprocal_laws a

let power_member (a:real{a >=. 1.0R}) (x:real{x >=. 0.0R}) (z:real)
  : Lemma (requires power_set a x z) (ensures z <=. power_ge_one a x)
  = power_lub a x

let power_upper (a:real{a >=. 1.0R}) (x:real{x >=. 0.0R}) (b:real)
  : Lemma (requires is_upper_bound (power_set a x) b) (ensures power_ge_one a x <=. b)
  = power_lub a x

let power_set_nat (a x z:real) (k:pos)
  : Lemma (requires a >=. 1.0R /\ x >=. 0.0R /\ power_set a x z)
          (ensures power_set a (x *. of_int k) (pow_nat z k))
  = eliminate exists (m:nat) (n:pos).
      of_int m <=. x *. of_int n /\ pow_nat z n <=. pow_nat a m
    with begin
      assert (m*k >= 0);
      scale_le (of_int m) (x *. of_int n) (of_int k);
      assert (of_int (m*k) <=. (x *. of_int k) *. of_int n);
      nat_mono (pow_nat z n) (pow_nat a m) k;
      nat_mul z n k;
      nat_mul z k n;
      nat_mul a m k;
      introduce exists (p:nat) (q:pos).
        of_int p <=. (x *. of_int k) *. of_int q /\
        pow_nat (pow_nat z k) q <=. pow_nat a p
      with (m*k) n and ()
    end

let power_set_root (a x z s:real) (k:pos)
  : Lemma (requires power_set a (x *. of_int k) z /\ s >=. 1.0R /\ pow_nat s k == z)
          (ensures power_set a x s)
  = eliminate exists (m:nat) (n:pos).
      of_int m <=. (x *. of_int k) *. of_int n /\ pow_nat z n <=. pow_nat a m
    with begin
      assert (k*n > 0);
      assert (of_int m <=. x *. of_int (k*n));
      nat_mul s k n;
      introduce exists (p:nat) (q:pos).
        of_int p <=. x *. of_int q /\ pow_nat s q <=. pow_nat a p
      with m (k*n) and ()
    end

/// Natural powers commute with the supremum defining real exponentiation.
let power_nat_scale (a:real{a >=. 1.0R}) (x:real{x >=. 0.0R}) (k:pos)
  : Lemma (pow_nat (power_ge_one a x) k == power_ge_one a (x *. of_int k))
  = let b = power_ge_one a x in
    let c = power_ge_one a (x *. of_int k) in
    let r = root c k in
    introduce forall (z:real). power_set a x z ==> z <=. r
    with introduce _ ==> _ with begin
      power_set_nat a x z k;
      power_member a (x *. of_int k) (pow_nat z k);
      nat_reflect z r k
    end;
    assert (is_upper_bound (power_set a x) r);
    power_upper a x r;
    nat_mono b r k;
    introduce forall (z:real). power_set a (x *. of_int k) z ==> z <=. pow_nat b k
    with introduce _ ==> _ with begin
      nat_ge_one b k;
      if z >=. 1.0R then begin
        let s = root z k in
        power_set_root a x z s k;
        power_member a x s;
        nat_mono s b k
      end
    end;
    assert (is_upper_bound (power_set a (x *. of_int k)) (pow_nat b k));
    power_upper a (x *. of_int k) (pow_nat b k)

let power_rational_scale (a:real{a >=. 1.0R}) (x:real{x >=. 0.0R}) (m:nat) (n:pos)
  : Lemma (power_ge_one (power_ge_one a x) (of_int m /. of_int n) ==
           power_ge_one a (x *. (of_int m /. of_int n)))
  = if m = 0 then begin
      power_nat (power_ge_one a x) 0;
      power_nat a 0
    end
    else begin
      power_nat_scale a x m;
      power_nat_scale a (x *. (of_int m /. of_int n)) n;
      power_rational_unique (power_ge_one a x) m n
        (power_ge_one a (x *. (of_int m /. of_int n)))
    end

let rec bernoulli (a:real{a >=. 1.0R}) (n:nat)
  : Lemma (pow_nat a n >=. 1.0R +. of_int n *. (a -. 1.0R)) (decreases n)
  = if n > 0 then begin
      bernoulli a (n-1);
      assert (a *. pow_nat a (n-1) >=.
              a *. (1.0R +. of_int (n-1) *. (a -. 1.0R)))
    end

let nat_unbounded (a:real{a >. 1.0R}) (b:real)
  : Lemma (exists (n:pos). pow_nat a n >. b)
  = archimedean ((b -. 1.0R) /. (a -. 1.0R));
    eliminate exists (n:nat). (b -. 1.0R) /. (a -. 1.0R) <. of_int n
    with begin
      bernoulli a (n+1);
      introduce exists (k:pos). pow_nat a k >. b with (n+1) and ()
    end

/// Rational exponents strictly below x suffice to bound a^x.
let power_strict_upper (a:real{a >=. 1.0R}) (x:real{x >=. 0.0R}) (b:real{b >=. 1.0R})
  : Lemma
      (requires forall (m:nat) (n:pos).
        of_int m <. x *. of_int n ==> pow_nat a m <=. pow_nat b n)
      (ensures power_ge_one a x <=. b)
  = introduce forall (z:real). power_set a x z ==> z <=. b
    with introduce power_set a x z ==> z <=. b with begin
      eliminate exists (m:nat) (n:pos).
        of_int m <=. x *. of_int n /\ pow_nat z n <=. pow_nat a m
      with begin
        introduce b <. z ==> False with begin
          nat_strict b z n;
          nat_ge_one b n;
          assert (m > 0);
          let u = pow_nat a m /. pow_nat b n in
          nat_unbounded u b;
          eliminate exists (k:pos). pow_nat u k >. b
          with begin
            assert (of_int (m*k) <. x *. of_int (n*k+1));
            assert (pow_nat a (m*k) <=. pow_nat b (n*k+1));
            nat_product u (pow_nat b n) k;
            nat_mul a m k;
            nat_mul b n k;
            pow_nat_succ b (n*k);
            nat_ge_one b (n*k);
            assert (u *. pow_nat b n == pow_nat a m);
            assert (pow_nat u k *. pow_nat b (n*k) >. b *. pow_nat b (n*k))
          end
        end
      end
    end;
    assert (is_upper_bound (power_set a x) b);
    power_upper a x b

let rec ceiling_bounded (x:real{x >=. 0.0R}) (k:nat)
  : Lemma (requires x <. of_int k)
          (ensures exists (m:nat). x <. of_int m /\ of_int m <=. x +. 1.0R)
          (decreases k)
  = if x <. of_int (k-1) then ceiling_bounded x (k-1)
    else introduce exists (m:nat). x <. of_int m /\ of_int m <=. x +. 1.0R
         with k and ()

let rational_between (x y:real{0.0R <=. x /\ x <. y})
  : Lemma (exists (m:nat) (n:pos). x <. of_int m /. of_int n /\ of_int m /. of_int n <. y)
  = archimedean (1.0R /. (y -. x));
    eliminate exists (n:nat). 1.0R /. (y -. x) <. of_int n
    with begin
      archimedean (x *. of_int n);
      eliminate exists (k:nat). x *. of_int n <. of_int k
      with begin
        ceiling_bounded (x *. of_int n) k;
        eliminate exists (m:nat).
          x *. of_int n <. of_int m /\ of_int m <=. x *. of_int n +. 1.0R
        with begin
          introduce exists (p:nat) (q:pos).
            x <. of_int p /. of_int q /\ of_int p /. of_int q <. y
          with m n and ()
        end
      end
    end

let ratio_scale (m:nat) (n:pos) (x:rpos) (q:real)
  : Lemma (requires of_int m /. (of_int n *. x) <=. q)
          (ensures of_int m /. of_int n <=. x *. q)
  = scale_le (of_int m /. (of_int n *. x)) q x;
    assert ((of_int m /. (of_int n *. x)) *. x == of_int m /. of_int n)

let power_power (a:real{a >=. 1.0R}) (x y:real{x >=. 0.0R /\ y >=. 0.0R})
  : Lemma (power_ge_one (power_ge_one a x) y == power_ge_one a (x *. y))
  = let b = power_ge_one a x in
    let c = power_ge_one b y in
    let d = power_ge_one a (x *. y) in
    introduce forall (m:nat) (n:pos).
      of_int m <. y *. of_int n ==> pow_nat b m <=. pow_nat d n
    with introduce of_int m <. y *. of_int n ==> pow_nat b m <=. pow_nat d n with begin
      if m = 0 then nat_ge_one d n
      else begin
        power_nat_scale a x m;
        power_nat_scale a (x *. y) n;
        power_mono a (x *. of_int m) ((x *. y) *. of_int n)
      end
    end;
    power_strict_upper b y d;
    introduce forall (m:nat) (n:pos).
      of_int m <. (x *. y) *. of_int n ==> pow_nat a m <=. pow_nat c n
    with introduce of_int m <. (x *. y) *. of_int n ==> pow_nat a m <=. pow_nat c n with begin
      assert (x >. 0.0R);
      rational_between (of_int m /. (of_int n *. x)) y;
      eliminate exists (k:nat) (l:pos).
        of_int m /. (of_int n *. x) <. of_int k /. of_int l /\ of_int k /. of_int l <. y
      with begin
        let q = of_int k /. of_int l in
        ratio_scale m n x q;
        power_mono b q y;
        power_rational_scale a x k l;
        power_mono a (of_int m /. of_int n) (x *. q);
        power_rational a m n;
        nat_mono (power_ge_one a (of_int m /. of_int n)) c n
      end
    end;
    power_strict_upper a (x *. y) c

let pow_pow_nonneg (a:rpos) (x y:real{x >=. 0.0R /\ y >=. 0.0R})
  : Lemma (pow (pow a x) y == pow a (x *. y))
  = if a >=. 1.0R then power_power a x y
    else begin
      let b = 1.0R /. a in
      power_power b x y;
      pow_inverse_base b x;
      pow_inverse_base (pow b x) y;
      pow_inverse_base b (x *. y);
      reciprocal_laws a
    end

let pow_pow_nonneg_outer (a:rpos) (x:real) (y:real{y >=. 0.0R})
  : Lemma (pow (pow a x) y == pow a (x *. y))
  = if x >=. 0.0R then pow_pow_nonneg a x y
    else begin
      let u = 0.0R -. x in
      pow_pow_nonneg a u y;
      pow_neg a u;
      pow_inverse_base (pow a u) y;
      pow_neg a (u *. y)
    end

let pow_pow (a:rpos) (x y:real)
  : Lemma (pow (pow a x) y == pow a (x *. y))
  = if y >=. 0.0R then pow_pow_nonneg_outer a x y
    else begin
      let v = 0.0R -. y in
      pow_pow_nonneg_outer a x v;
      pow_neg (pow a x) v;
      pow_neg a (x *. v)
    end
