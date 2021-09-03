module ClassicalSugar

let test_elim_exists_1 p (x z:nat)
                       (trans: (x:nat -> y:nat -> z:nat ->
                                Lemma (requires p x y /\ p y z)
                                      (ensures p x z)))
  : Lemma
    (requires
      (exists y. p x y /\ p y z))
    (ensures
      p x z)
  = eliminate exists y.
         p x y /\ p y z
    returns p x z
    with _.
       trans x y z

let test_elim_exists_2 p x z
                       (_:squash (exists y. p x y /\ p y z))
                       (trans : (#x:_ -> #y:_ -> #z:_ -> squash (p x y /\ p y z) -> squash (p x z)))
  : squash (p x z)
  = eliminate exists (y:nat).
         p x y /\ p y z
    returns p x z
    with pf. (
       trans pf
    )

let test_elim_exists_3 p
                       (trans: (x:nat -> y:nat -> z:nat ->
                                Lemma (requires p x y /\ p y z)
                                      (ensures p x z)))
                       (x z:nat)
  : Lemma
    (requires
      (exists y0 y1. p x y0 /\ p y0 y1 /\ p y1 z))
    (ensures
      p x z)
  = eliminate exists y0 y1.
       p x y0 /\ p y0 y1 /\ p y1 z
    returns p x z
    with  _. (
       trans y0 y1 z;
       trans x y0 z
    )

let test_elim_forall_1 p (_:squash (forall x y. p x y))
  : squash (p 0 1)
  = eliminate forall x y. p x y
    with 0 1

let test_elim_forall_2 (p: nat -> nat -> Type)
  : Lemma
    (requires (forall x y. p x y))
    (ensures p 0 1)
  = eliminate forall x y. p x y
    with 0 1

let test_elim_implies_1 p q (_:squash (p ==> q)) (x:squash p)
 : Tot (squash q)
  = eliminate p ==> q
    with x

let test_elim_implies_2 p q (f: unit -> Lemma p)
  : Lemma (requires (p ==> q))
          (ensures q)
  = eliminate p ==> q
    with f()

let test_elim_or_1 p q r (_:squash (p \/ q))  (f: squash p -> squash r) (g:squash q -> squash r)
  : squash r
  = eliminate p \/ q
    returns r
    with pf_p. f pf_p
    and  pf_q. g pf_q

let test_elim_or_2 p q r
                   (f: unit -> Lemma (requires p) (ensures r))
                   (g: unit -> Lemma (requires q) (ensures r))
  : Lemma (requires p \/ q)
          (ensures r)
  = eliminate p \/ q
    returns r
    with _p. f ()
    and  _q. g ()

let test_elim_and_1 p q r (_:squash (p /\ q))  (f: squash p -> squash q -> squash r)
  : squash r
  = eliminate p /\ q
    returns r
    with pf_p pf_q. f pf_p pf_q

let test_elim_and_2 p q r (f: squash p -> squash q -> Lemma r)
  : Lemma
    (requires p /\ q)
    (ensures r)
  = eliminate p /\ q
    returns r
    with pf_p pf_q. f pf_p pf_q

////////////////////////////////////////////////////////////////////////////////
let test_forall_intro_1 #a #b #c (p: a -> b -> c -> Type)
                      (f:(x:a -> y:b -> z:c -> squash (p x y z)))
  : squash (forall x y z. p x y z)
  = introduce forall x y z. p x y z
    with f x y z

let test_forall_intro_2 #a #b #c (p: a -> b -> c -> Type)
                      (f:(x:a -> y:b -> z:c -> Lemma (p x y z)))
  : Lemma (forall x y z. p x y z)
  = introduce
    forall x y z. p x y z
        with f x y z

let test_exists_intro_1 #a #b #c (p: a -> b -> c -> Type) va vb vc
                        (f:squash (p va vb vc))
  : squash (exists x y z. p x y z)
  = introduce exists x y z. p x y z
    with va vb vc
    and f

let test_exists_intro_2 #a #b #c (p: a -> b -> c -> Type) va vb vc
                        (f:unit -> Lemma (p va vb vc))
  : Lemma (exists x y z. p x y z)
  = introduce exists x y z. p x y z
    with va vb vc
    and f()

let test_implies_intro_1 p q (f: squash p -> squash q)
  : squash (p ==> q)
  = introduce p ==> q
    with x. f x

let test_implies_intro_2 p q (f: unit -> Lemma (requires p) (ensures q))
  : Lemma (p ==> q)
  = introduce p ==> q
    with _. f ()

let test_or_intro_left_1 p q (f: squash p)
  : squash (p \/ q)
  = introduce p \/ q
    with Left f

let test_or_intro_left_2 p q (f: unit -> Lemma p)
  : squash (p \/ q)
  = introduce p \/ q
    with Left (f())

let test_or_intro_right_1 p q (f: squash q)
  : squash (p \/ q)
  = introduce p \/ q
    with Right f

let test_or_intro_right_2 p q (f: unit -> Lemma q)
  : squash (p \/ q)
  = introduce p \/ q
    with Right (f())

let test_and_intro_1 p q (f:squash p) (g:squash q)
  : squash (p /\ q)
  = introduce p /\ q
    with f
    and g

let test_and_intro_2 p q (f:unit -> Lemma p) (g:unit -> Lemma q)
  : Lemma (p /\ q)
  = introduce p /\ q
    with f()
    and g()

////////////////////////////////////////////////////////////////////////////////
//derived forms
////////////////////////////////////////////////////////////////////////////////
let test_excluded_middle p r
                   (f: unit -> Lemma (requires p) (ensures r))
                   (g: unit -> Lemma (requires ~p) (ensures r))
  : Lemma r
  = eliminate p \/ ~p
    returns r
    with _. f ()
    and  _. g ()

let test_forall_implies a (p:a -> Type) (q:a -> Type) (f: (x:a -> squash (p x) -> squash (q x)))
  : squash (forall x. p x ==> q x)
  = introduce forall x. p x ==> q x
    with introduce _ ==> _
         with px. (
           f x px
         )

let test_forall_implies_2_1 a (p:a -> Type) (q:a -> Type) (f: (x:a -> Lemma (requires p x) (ensures q x)))
  : Lemma (forall x. p x ==> q x)
  = introduce forall x. p x ==> q x
    with introduce _ ==> _
         with _. (
           assert (p x);
           f x;
           assert (q x)
         )

let test_forall_implies_2_2 a (p:a -> Type) (q:a -> Type) (f: (x:a -> Lemma (requires p x) (ensures q x)))
  : Lemma (forall x. p x ==> q x)
  = introduce forall x. _
    with introduce p x ==> q x
         with _. f x

let test_forall_implies_2_3 a (p:a -> Type) (q:a -> Type) (f: (x:a -> Lemma (requires p x) (ensures q x)))
  : Lemma (forall x. p x ==> q x)
  = introduce forall x. _
    with introduce p x ==> _
         with _. (
           f x <: squash (q x)
         )

////////////////////////////////////////////////////////////////////////////////
// Some more tests, checking that the L-to-R well-typedness bias is preserved
////////////////////////////////////////////////////////////////////////////////
let test_bias_implies (f: nat -> nat { forall x. f x = x + 1 })
                      (x: int)
  : Lemma (ensures x >= 0 ==> f x == x + 1) =
    introduce x >= 0 ==> f x == x + 1
    with _. ()

[@@"opaque_to_smt"]
let is_nat (x:int) = x >= 0
let test_bias_and (f: nat -> nat { forall x. f x = x + 1 })
                  (x: int)
  : Lemma
    (requires is_nat x)
    (ensures x >= 0 /\ f x == x + 1)
  = introduce x >= 0 /\ f x == x + 1
    with reveal_opaque (`%is_nat) is_nat
    and ()

let test_bias_or (f: nat -> nat { forall x. f x = x + 1 })
                 (x: int)
  : Lemma (x < 0 \/ f x = x + 1)
  = eliminate (x < 0) \/ (x >= 0)
    returns (x < 0 \/ f x = x + 1)
    with _. introduce _ \/ _ with Left ()
    and _. introduce _ \/ _ with Right ()

let test_bias_or_alt (f: nat -> nat { forall x. f x = x + 1 })
                 (x: int)
  : Lemma (x < 0 \/ f x = x + 1)
  = eliminate ~(is_nat x) \/ is_nat x
    returns (x < 0 \/ f x = x + 1)
    with _. introduce _ \/ _ with Left (reveal_opaque (`%is_nat) is_nat)
    and _. introduce _ \/ _ with Right (reveal_opaque (`%is_nat) is_nat)

////////////////////////////////////////////////////////////////////////////////
// Some more tests, checking that admits don't discard the continuation
////////////////////////////////////////////////////////////////////////////////

let admit_implies_elim p q (_:squash (p ==> q))
  = eliminate p ==> q
    with admit();
    assert q

[@@expect_failure [19]]
let admit_implies_elim_fail p q r (_:squash (p ==> q))
  = eliminate p ==> q
    with admit();
    assert r

let admit_or_intro_left p q
  = let _ = introduce p \/ q
            with Left admit()
    in
    assert (p \/ q)

let admit_or_intro_right p q
  = let _ = introduce p \/ q
            with Right admit()
    in
    assert (p \/ q)

[@@expect_failure [19]]
let admit_or_intro_left_fail p q r
  = let _ = introduce p \/ q
            with Left admit()
    in
    assert r

[@@expect_failure [19]]
let admit_or_intro_right_fail p q r
  = let _ = introduce p \/ q
            with Right admit()
    in
    assert r


let admit_and_intro p q
  = let _ = introduce p /\ q
            with admit()
            and admit()
    in
    assert (p /\ q)

[@@expect_failure [19]]
let admit_and_intro_fail p q r
  = let _ = introduce p /\ q
            with admit()
            and admit()
    in
    assert r

[@@expect_failure [19]]
let admit_and_intro_fail_branch p q
  = let _ = introduce p /\ q
            with admit() //this admit does't pollute the other branch
            and ()
    in
    assert (p /\ q)
