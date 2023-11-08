module Pulse.Lib.OnRange
open Pulse.Lib.Pervasives
open Pulse.Lib.Stick

val on_range (p: (nat -> vprop))
             ([@@@equate_by_smt] i:nat)
             ([@@@equate_by_smt] j:nat)
  : vprop

val on_range_le
  (#opened: _)
  (p: (nat -> vprop))
  (#i:nat)
  (#j:nat)
: stt_ghost unit opened
    (requires on_range p i j)
    (ensures fun _ -> on_range p i j ** pure (i <= j))

val on_range_empty
  (#opened: _)
  (p: (nat -> vprop))
  (i: nat)
: stt_ghost unit opened
    (requires emp)
    (ensures fun _ -> on_range p i i)

val on_range_singleton_intro
  (#opened: _)
  (p: (nat -> vprop))
  (i: nat)
: stt_ghost unit opened
    (requires (p i))
    (ensures fun _ -> on_range p i (i + 1))

val on_range_singleton_elim
  (#opened: _)
  (_:unit)
  (#p: (nat -> vprop))
  (#i:nat)
  (#j:nat { j == i + 1 })
: stt_ghost unit opened
    (on_range p i j)
    (fun _ -> p i)

val on_range_split
  (#opened: _)
  (j:nat)
  (#p: (nat -> vprop))
  (#i:nat{ i <= j })
  (#k:nat{ j <= k })
: stt_ghost unit opened
    (requires on_range p i k)
    (ensures fun _ -> on_range p i j ** on_range p j k)

val on_range_join
  (#opened: _)
  (i j k: nat)
  (#p: (nat -> vprop))
: stt_ghost unit opened
    (requires on_range p i j ** on_range p j k)
    (ensures fun _ -> on_range p i k)

val on_range_cons
  (#opened: _)
  (i:nat)
  (#p: (nat -> vprop))
  (#j:nat{j == i + 1})
  (#k: nat)
: stt_ghost unit opened
    (p i ** on_range p j k)
    (fun _ -> on_range p i k)

val on_range_uncons
  (#opened: _)
  (_:unit)
  (#p: (nat -> vprop))
  (#i:nat)
  (#k:nat { i < k })
: stt_ghost unit opened
    (on_range p i k)
    (fun _ -> p i ** on_range p (i + 1) k)

val on_range_cons_with_implies
  (#opened: _)
  (i:nat)
  (#p: (nat -> vprop))
  (#k: nat)
: stt_ghost unit opened
    (p i ** on_range p (i + 1) k)
    (fun _ ->
      on_range p i k **
      (on_range p i k @==> (p i ** on_range p (i + 1) k))
    )

val on_range_snoc
  (#opened: _)
  (_:unit)
  (#p: (nat -> vprop))
  (#i #j:nat)
: stt_ghost unit opened
    (on_range p i j ** p j)
    (fun _ -> on_range p i (j + 1))

val on_range_unsnoc
  (#opened: _)
  (_:unit)
  (#p: (nat -> vprop))
  (#i:nat)
  (#k:nat{ i < k })
: stt_ghost unit opened
    (on_range p i k)
    (fun _ -> on_range p i (k - 1) ** p (k - 1))

val on_range_snoc_with_implies
  (#opened: _)
  (_:unit)
  (#p: (nat -> vprop))
  (#i:nat)
  (#j:nat)
: stt_ghost unit opened
    (on_range p i j ** p j)
    (fun _ -> on_range p i (j + 1) **  (on_range p i (j + 1) @==> (on_range p i j ** p j)))

val on_range_get
  (#opened: _)
  (j:nat)
  (#p: (nat -> vprop))
  (#i:nat{i <= j})
  (#k:nat{j < k})
: stt_ghost unit opened
    (on_range p i k)
    (fun _ -> on_range p i j ** p j ** on_range p (j + 1) k)

val on_range_put
  (#opened: _)
  (i:nat)
  (j:nat{ i <= j })
  (k:nat{ j < k })
  (#p: (nat -> vprop))
: stt_ghost unit opened
    (on_range p i j ** p j ** on_range p (j + 1) k)
    (fun _ -> on_range p i k)
 
val on_range_focus
  (#opened: _)
  (j:nat)
  (#p: (nat -> vprop))
  (#i:nat{ i <= j })
  (#k:nat{ j < k })
: stt_ghost unit opened
    (on_range p i k)
    (fun _ -> p j ** (p j @==> on_range p i k))

val on_range_weaken_and_shift
  (#opened: _)
  (p p': (nat -> vprop))
  (delta: int)
  (i: nat { i + delta >= 0 })
  (j: nat { j + delta >= 0 })
  (* maybe phi could open some invariants too? *)
  (phi: (k: nat { i <= k /\ k < j }) -> stt_ghost unit opened (p k) (fun _ -> p' (k + delta)))
: stt_ghost unit opened
    (on_range p i j)
    (fun _ -> on_range p' (i + delta) (j + delta))

val on_range_weaken
  (#opened: _)
  (p p': (nat -> vprop))
  (i: nat)
  (j: nat)
  (* maybe phi could open some invariants too? *)
  (phi: (k: nat { i <= k /\ k < j }) -> stt_ghost unit opened (p k) (fun _ -> p' k))
: stt_ghost unit opened
    (on_range p i j)
    (fun _ -> on_range p' i j)
