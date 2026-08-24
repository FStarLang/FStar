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
    with
       trans x y z

let test_elim_exists_2 p x z
                       (_:squash (exists y. p x y /\ p y z))
                       (trans : (#x:_ -> #y:_ -> #z:_ -> squash (p x y /\ p y z) -> squash (p x z)))
  : squash (p x z)
  = eliminate exists (y:nat).
         p x y /\ p y z
    with (
       trans #x #y #z ()
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
    with (
       trans y0 y1 z;
       trans x y0 z
    )

let test_elim_forall_1 p (_:squash (forall x y. p x y))
  : squash (p 0 1)
  = eliminate forall x y. p x y
    with 0 1

let test_elim_forall_2 (p: nat -> nat -> prop)
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
    with f ()
    and g ()

let test_elim_or_2 p q r
                   (f: unit -> Lemma (requires p) (ensures r))
                   (g: unit -> Lemma (requires q) (ensures r))
  : Lemma (requires p \/ q)
          (ensures r)
  = eliminate p \/ q
    with f ()
    and g ()

let test_elim_and_1 p q r (_:squash (p /\ q))  (f: squash p -> squash q -> squash r)
  : squash r
  = eliminate p /\ q
    with f () ()

let test_elim_and_2 p q r (f: squash p -> squash q -> Lemma r)
  : Lemma
    (requires p /\ q)
    (ensures r)
  = eliminate p /\ q
    with f () ()

////////////////////////////////////////////////////////////////////////////////
let test_forall_intro_1 #a #b #c (p: a -> b -> c -> prop)
                      (f:(x:a -> y:b -> z:c -> squash (p x y z)))
  : squash (forall x y z. p x y z)
  = introduce forall x y z. p x y z
    with f x y z

let test_forall_intro_2 #a #b #c (p: a -> b -> c -> prop)
                      (f:(x:a -> y:b -> z:c -> Lemma (p x y z)))
  : Lemma (forall x y z. p x y z)
  = introduce
    forall x y z. p x y z
        with f x y z

let test_exists_intro_1 #a #b #c (p: a -> b -> c -> prop) va vb vc
                        (f:squash (p va vb vc))
  : squash (exists x y z. p x y z)
  = introduce exists x y z. p x y z
    with va vb vc
    and f

let test_exists_intro_2 #a #b #c (p: a -> b -> c -> prop) va vb vc
                        (f:unit -> Lemma (p va vb vc))
  : Lemma (exists x y z. p x y z)
  = introduce exists x y z. p x y z
    with va vb vc
    and f()

let test_implies_intro_1 p q (f: squash p -> squash q)
  : squash (p ==> q)
  = introduce p ==> q
    with f ()

let test_implies_intro_2 p q (f: unit -> Lemma (requires p) (ensures q))
  : Lemma (p ==> q)
  = introduce p ==> q
    with f ()

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
    with f ()
    and g ()

let test_forall_implies a (p:a -> prop) (q:a -> prop) (f: (x:a -> squash (p x) -> squash (q x)))
  : squash (forall x. p x ==> q x)
  = introduce forall x. p x ==> q x
    with introduce _ ==> _
         with (
           f x ()
         )

let test_forall_implies_2_1 a (p:a -> prop) (q:a -> prop) (f: (x:a -> Lemma (requires p x) (ensures q x)))
  : Lemma (forall x. p x ==> q x)
  = introduce forall x. p x ==> q x
    with introduce _ ==> _
         with (
           assert (p x);
           f x;
           assert (q x)
         )

let test_forall_implies_2_2 a (p:a -> prop) (q:a -> prop) (f: (x:a -> Lemma (requires p x) (ensures q x)))
  : Lemma (forall x. p x ==> q x)
  = introduce forall x. _
    with introduce p x ==> q x
         with f x

let test_forall_implies_2_3 a (p:a -> prop) (q:a -> prop) (f: (x:a -> Lemma (requires p x) (ensures q x)))
  : Lemma (forall x. p x ==> q x)
  = introduce forall x. _
    with introduce p x ==> _
         with (
           f x <: squash (q x)
         )

////////////////////////////////////////////////////////////////////////////////
// Some more tests, checking that the L-to-R well-typedness bias is preserved
////////////////////////////////////////////////////////////////////////////////
let test_bias_implies (f: nat -> nat { forall x. f x = x + 1 })
                      (x: int)
  : Lemma (ensures x >= 0 ==> f x == x + 1) =
    introduce x >= 0 ==> f x == x + 1
    with ()

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
    with introduce (x < 0) \/ (f x = x + 1) with Left ()
    and introduce (x < 0) \/ (f x = x + 1) with Right ()

let test_bias_or_alt (f: nat -> nat { forall x. f x = x + 1 })
                 (x: int)
  : Lemma (x < 0 \/ f x = x + 1)
  = eliminate ~(is_nat x) \/ is_nat x
    with introduce (x < 0) \/ (f x = x + 1) with Left (reveal_opaque (`%is_nat) is_nat)
    and introduce (x < 0) \/ (f x = x + 1) with Right (reveal_opaque (`%is_nat) is_nat)

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

////////////////////////////////////////////////////////////////////////////////
// eliminate exists with dependently typed and with many binders
////////////////////////////////////////////////////////////////////////////////
let test_elim_exists_dependent (t: int -> Type) (p: (x:int -> t x -> prop))
  : Lemma
    (requires exists (x:int) (y:t x). p x y)
    (ensures exists (x:int) (y:t x). p x y)
  = eliminate exists (x:int) (y:t x). p x y
    with ()

// Up to max_indefinite_description_arity binders are taken in a single call.
let test_elim_exists_7 (p: int -> int -> int -> int -> int -> int -> int -> prop)
  : Lemma
    (requires exists a b c d e f g. p a b c d e f g)
    (ensures exists a b c d e f g. p a b c d e f g)
  = eliminate exists a b c d e f g. p a b c d e f g
    with ()

// More binders than max_indefinite_description_arity: the desugaring peels off
// one binder at a time down to a final n-ary call. This used to need a huge
// rlimit (issue #4405) and, later, minutes of elaboration (issue #4444).
let test_elim_exists_15
      (p: int -> int -> int -> int -> int -> int -> int -> int
          -> int -> int -> int -> int -> int -> int -> int -> prop)
  : Lemma
    (requires exists a b c d e f g h i j k l m n o. p a b c d e f g h i j k l m n o)
    (ensures exists a b c d e f g h i j k l m n o. p a b c d e f g h i j k l m n o)
  = eliminate exists a b c d e f g h i j k l m n o. p a b c d e f g h i j k l m n o
    with ()

let test_elim_exists_witness (p: int -> prop) (f: (x:int -> squash (p x) -> squash False))
  : Lemma (requires exists x. p x) (ensures False)
  = eliminate exists x. p x
    with f x ()

// A projection right after `with` is not mistaken for an obsolete hypothesis name
noeq
type eqrel = {
  rel: int -> int -> prop;
  sym: (x:int -> y:int -> Lemma (requires rel x y) (ensures rel y x));
}
let test_intro_implies_projection (eq:eqrel) (x y:int)
  : squash (eq.rel x y ==> eq.rel y x)
  = introduce eq.rel x y ==> eq.rel y x
    with eq.sym x y
