module Steel.ST.OnRange
include Steel.ST.Util

val on_range (p: (nat -> vprop)) (i j: nat) : vprop

val on_range_le
  (#opened: _)
  (p: (nat -> vprop))
  (i j: nat)
: STGhost unit opened
    (on_range p i j)
    (fun _ -> on_range p i j)
    True
    (fun _ -> i <= j)

val on_range_empty
  (#opened: _)
  (p: (nat -> vprop))
  (i: nat)
  (j: nat)
: STGhost unit opened
    emp
    (fun _ -> on_range p i j)
    (i == j)
    (fun _ -> True)

val on_range_singleton_intro
  (#opened: _)
  (p: (nat -> vprop))
  (i: nat)
  (j: nat)
: STGhost unit opened
    (p i)
    (fun _ -> on_range p i j)
    (j == i + 1)
    (fun _ -> True)

val on_range_singleton_elim
  (#opened: _)
  (p: (nat -> vprop))
  (i j: nat)
: STGhost unit opened
    (on_range p i j)
    (fun _ -> p i)
    (j == i + 1)
    (fun _ -> True)

val on_range_split
  (#opened: _)
  (p: (nat -> vprop))
  (i j k: nat)
: STGhost unit opened
    (on_range p i k)
    (fun _ -> on_range p i j `star` on_range p j k)
    (i <= j /\ j <= k)
    (fun _ -> True)

val on_range_join
  (#opened: _)
  (p: (nat -> vprop))
  (i j k: nat)
: STGhostT unit opened
    (on_range p i j `star` on_range p j k)
    (fun _ -> on_range p i k)

let on_range_cons
  (#opened: _)
  (p: (nat -> vprop))
  (i j k: nat)
: STGhost unit opened
    (p i `star` on_range p j k)
    (fun _ -> on_range p i k)
    (j == i + 1)
    (fun _ -> True)
= on_range_singleton_intro p i j;
  on_range_join p i j k

let on_range_uncons
  (#opened: _)
  (p: (nat -> vprop))
  (i j k: nat)
: STGhost unit opened
    (on_range p i k)
    (fun _ -> p i `star` on_range p j k)
    (j == i + 1 /\ j <= k)
    (fun _ -> True)
= on_range_split p i j k;
  on_range_singleton_elim p i j

let on_range_snoc
  (#opened: _)
  (p: (nat -> vprop))
  (i j j' k: nat)
: STGhost unit opened
    (on_range p i j `star` p j')
    (fun _ -> on_range p i k)
    (j' == j /\ k == j + 1)
    (fun _ -> True)
= rewrite (p j') (p j);
  on_range_singleton_intro p j k;
  on_range_join p i j k

let on_range_unsnoc
  (#opened: _)
  (p: (nat -> vprop))
  (i j k: nat)
: STGhost unit opened
    (on_range p i k)
    (fun _ -> on_range p i j `star` p j)
    (i <= j /\ k == j + 1)
    (fun _ -> True)
= on_range_split p i j k;
  on_range_singleton_elim p j k

let on_range_get
  (#opened: _)
  (p: (nat -> vprop))
  (i j k l: nat)
: STGhost unit opened
    (on_range p i l)
    (fun _ -> on_range p i j `star` p j `star` on_range p k l)
    (i <= j /\ j + 1 == k /\ k <= l)
    (fun _ -> True)
= on_range_split p i j l;
  on_range_split p j k l;
  on_range_singleton_elim p j k

let on_range_put
  (#opened: _)
  (p: (nat -> vprop))
  (i j k l m: nat)
: STGhost unit opened
    (on_range p i j `star` p k `star` on_range p l m)
    (fun _ -> on_range p i m)
    (j == k /\ k + 1 == l)
    (fun _ -> True)
= rewrite (p k) (p j);
  on_range_singleton_intro p j l;
  on_range_join p i j l;
  on_range_join p i l m

let on_range_focus
  (#opened: _)
  (p: (nat -> vprop))
  (i j k: nat)
: STGhost unit opened
    (on_range p i k)
    (fun _ -> p j `star` (p j `implies_` on_range p i k))
    (i <= j /\ j < k)
    (fun _ -> True)
= on_range_get p i j (j + 1) k;
  intro_implies
    (p j)
    (on_range p i k)
    (on_range p i j `star` on_range p (j + 1) k)
    (fun _ ->
      on_range_put p i j j (j + 1) k
    )

let rec on_range_weaken_and_shift
  (#opened: _)
  (p p': (nat -> vprop))
  (delta: int)
  (i: nat { i + delta >= 0 })
  (j: nat)
  (phi: (k: nat { i <= k /\ k < j }) -> STGhostT unit opened (p k) (fun _ -> p' (k + delta)))
  (i': nat { i' == i + delta })
  (j': nat { j' == j + delta })
: STGhostT unit opened
    (on_range p i j)
    (fun _ -> on_range p' i' j')
    (decreases (if j >= i then j - i else 0))
= on_range_le p i j;
  if j <= i
  then begin
    drop (on_range p i j);
    on_range_empty p' i' j'
  end else begin
    on_range_split p i (i + 1) j;
    on_range_singleton_elim p i (i + 1);
    phi i;
    rewrite (p' _) (p' i');
    on_range_singleton_intro p' i' (i' + 1);
    on_range_weaken_and_shift p p' delta (i + 1) j phi (i' + 1) j';
    on_range_join p' i' (i' + 1) j'
  end

let on_range_weaken
  (#opened: _)
  (p p': (nat -> vprop))
  (i: nat)
  (j: nat)
  (phi: (k: nat { i <= k /\ k < j }) -> STGhostT unit opened (p k) (fun _ -> p' k))
: STGhostT unit opened
    (on_range p i j)
    (fun _ -> on_range p' i j)
= on_range_weaken_and_shift
    p p'
    0
    i j
    (fun k -> phi k; rewrite (p' k) (p' (k + 0)))
    i j
