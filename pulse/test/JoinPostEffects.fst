module JoinPostEffects
#lang-pulse
open Pulse
open Pulse.Lib.Reference
open Pulse.Lib.Primitives
module GR = Pulse.Lib.GhostReference
module B = Pulse.Lib.Box
module U32 = FStar.UInt32

(* The effect of an `if` that is not the last statement, and whose
   postcondition is inferred. It is computed from the natural effects of the
   branches, as when composing two computations: divergence wins over stt,
   which wins over atomic and ghost; ghost and atomic branches keep their
   effect, over the join of their invariant names. *)

divergent fn diverge ()
  requires emp
  ensures emp
{
  while (true) invariant emp { () }
}

ghost fn leak (x:erased int)
  returns y:int
  ensures pure (y == reveal x)
{
  reveal x
}

unobservable fn bump (r:GR.ref int)
  requires GR.pts_to r 'v
  ensures GR.pts_to r ('v + 1)
{
  GR.(r := 'v + 1)
}

unobservable fn bump_get (r:GR.ref int)
  requires GR.pts_to r 'v
  returns y:int
  ensures GR.pts_to r ('v + 1) ** pure (y == 0)
{
  GR.(r := 'v + 1);
  0
}

ghost fn step (i:iname)
  requires emp
  ensures emp
  opens [i]
{
  ()
}

(* Divergent *)

divergent fn div_writes_differ (b:bool) (r:ref int)
  requires r |-> 0
  ensures exists* v. r |-> v
{
  if (b) { r := 1; diverge () } else { r := 2; };
  r := 3;
}

divergent fn div_one_side (b:bool) (r:ref int)
  requires r |-> 0
  ensures exists* v. r |-> v
{
  if (b) { diverge (); r := 1; } else { () };
  let x = !r;
  ()
}

divergent fn div_and_ghost (b:bool) (r:GR.ref int)
  requires GR.pts_to r 0
  ensures exists* v. GR.pts_to r v
{
  if (b) { diverge () } else { GR.(r := 2) };
  ()
}

[@@expect_failure [228]]
fn div_in_stt (b:bool) (r:ref int)
  requires r |-> 0
  ensures exists* v. r |-> v
{
  if (b) { r := 1; diverge () } else { r := 2; };
  ()
}

(* Ghost *)

ghost fn ghost_writes_differ (b:bool) (r:GR.ref int)
  requires GR.pts_to r 0
  ensures exists* v. GR.pts_to r v
{
  if (b) { GR.(r := 1) } else { GR.(r := 2) };
  ()
}

ghost fn ghost_annotated (b:bool) (r:GR.ref int)
  requires GR.pts_to r 0
  ensures exists* v. GR.pts_to r v
{
  if (b) ensures exists* v. GR.pts_to r v { GR.(r := 1) } else { GR.(r := 2) };
  ()
}

ghost fn ghost_no_state (b:bool)
{
  if (b) { () } else { () };
  ()
}

ghost fn ghost_result (b:bool)
{
  let x : int = if (b) { 1 } else { 2 };
  assert (pure (x == 1 \/ x == 2))
}

(* An informative result is fine in ghost code. *)
ghost fn ghost_informative (b:bool) (x:erased int)
  returns y:int
  ensures pure (b ==> y == reveal x)
{
  let y = if (b) { leak x } else { 0 };
  y
}

ghost fn ghost_sequenced (b c:bool) (r:GR.ref int)
  requires GR.pts_to r 0
  ensures exists* v. GR.pts_to r v
{
  if (b) { GR.(r := 1) } else { () };
  if (c) { GR.(r := 2) } else { () };
  ()
}

(* The branches open different invariants. *)
ghost fn ghost_inames (b:bool) (i j:iname)
  requires emp
  ensures emp
  opens [i; j]
{
  if (b) { step i } else { step j };
  ()
}

[@@expect_failure [19]]
ghost fn ghost_inames_too_many (b:bool) (i j:iname)
  requires emp
  ensures emp
  opens [i]
{
  if (b) { step i } else { step j };
  ()
}

[@@expect_failure [228]]
ghost fn ghost_stt_branch (b:bool) (r:ref int)
  requires r |-> 0
  ensures exists* v. r |-> v
{
  if (b) { r := 1 } else { r := 2 };
  ()
}

(* Atomic *)

atomic fn atomic_writes_differ (b:bool) (r:B.box U32.t)
  requires r |-> 0ul
  ensures exists* v. r |-> v
{
  if (b) { write_atomic_box r 1ul } else { write_atomic_box r 2ul };
  ()
}

atomic fn atomic_and_ghost (b:bool) (r:B.box U32.t) (g:GR.ref int)
  requires (r |-> 0ul) ** GR.pts_to g 0
  ensures exists* v w. (r |-> v) ** GR.pts_to g w
{
  if (b) { write_atomic_box r 1ul } else { GR.(g := 1) };
  ()
}

(* An unobservable conditional followed by an observable step. *)
atomic fn atomic_unobservable (b:bool) (r:B.box U32.t) (g:GR.ref int)
  requires (r |-> 0ul) ** GR.pts_to g 0
  ensures exists* v w. (r |-> v) ** GR.pts_to g w
{
  if (b) { bump g } else { () };
  write_atomic_box r 5ul
}

(* A ghost branch with an informative result and an unobservable branch: the
   conditional is ghost. *)
ghost fn ghost_and_unobservable (b:bool) (x:erased int) (g:GR.ref int)
  requires GR.pts_to g 0
  returns y:int
  ensures (exists* v. GR.pts_to g v) ** pure (b ==> y == reveal x)
{
  let y = if (b) { leak x } else { bump_get g };
  y
}

(* ... but not with an observable branch. *)
[@@expect_failure [228]]
atomic fn atomic_ghost_informative (b:bool) (x:erased int) (r:B.box U32.t)
  requires r |-> 0ul
  returns y:int
  ensures exists* v. r |-> v
{
  let y = if (b) { leak x } else { write_atomic_box r 1ul; 0 };
  y
}

(* Two observable steps. *)
[@@expect_failure [228]]
atomic fn atomic_two_observable (b:bool) (r:B.box U32.t)
  requires r |-> 0ul
  ensures exists* v. r |-> v
{
  if (b) { write_atomic_box r 1ul } else { write_atomic_box r 2ul };
  write_atomic_box r 3ul
}

[@@expect_failure [228]]
atomic fn atomic_stt_branch (b:bool) (r:ref int)
  requires r |-> 0
  ensures exists* v. r |-> v
{
  if (b) { r := 1 } else { r := 2 };
  ()
}

(* stt *)

fn stt_ghost_branches (b:bool) (r:GR.ref int) (s:ref int)
  requires GR.pts_to r 0 ** s |-> 0
  ensures exists* v. GR.pts_to r v ** s |-> 5
{
  if (b) { GR.(r := 1) } else { GR.(r := 2) };
  s := 5
}

fn stt_and_ghost (b:bool) (r:GR.ref int) (s:ref int)
  requires GR.pts_to r 0 ** s |-> 0
  ensures exists* v w. GR.pts_to r v ** s |-> w
{
  if (b) { GR.(r := 1) } else { s := 1 };
  s := 5
}

fn stt_atomic_branch (b:bool) (r:B.box U32.t)
  requires r |-> 0ul
  ensures exists* v. r |-> v
{
  if (b) { write_atomic_box r 1ul } else { () };
  let x = read_atomic_box r;
  ()
}

(* A ghost value with an informative type cannot flow into concrete code
   through a conditional. *)
[@@expect_failure [228]]
fn stt_ghost_informative (b:bool) (x:erased int)
  returns y:int
  ensures pure (b ==> y == reveal x)
{
  let y = if (b) { leak x } else { 0 };
  y
}
