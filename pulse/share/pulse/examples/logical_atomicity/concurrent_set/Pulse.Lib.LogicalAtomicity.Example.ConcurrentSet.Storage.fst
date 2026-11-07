module Pulse.Lib.LogicalAtomicity.Example.ConcurrentSet.Storage
#lang-pulse

(**
Per-node locks and fractional shadow links for the lock-coupling set.

The lock protects the physical next field and half of its ghost shadow.
The set invariant owns the other half. Agreement lets a lock holder relate
its edge to the current abstract set; neither side can change that edge
without the other. This replaces the paper's oldNext ghost fields and node
membership bag with a finite, total registry of shadow links.

Lock handles are fractionally shared, not leaked: acquire borrows a handle
from the registry and release gathers it back. Runtime synchronization uses
Pulse.Lib.SpinLock's existing native realization, one mutex per node.
*)

open Pulse.Lib.Pervasives
module B = Pulse.Lib.Box
module G = Pulse.Lib.GhostReference
module Lock = Pulse.Lib.SpinLock
module L = FStar.List.Tot

(** An open lock lends precisely the physical edge and its agreeing ghost half. *)
let protected (next:B.box nat) (shadow:G.ref nat) =
  exists* v. B.pts_to next v ** G.pts_to shadow #0.5R v

noeq type cell = { next:B.box nat; shadow:G.ref nat; lock:Lock.lock }
let at (cells:list cell) (k:nat { k < L.length cells }) = L.index cells k
let access (c:cell) = exists* (p:perm). Lock.lock_alive c.lock #p (protected c.next c.shadow)

(** A handle may be duplicated, but the resources protected by it may not. *)
ghost fn dup_access (c:cell) ()
  requires access c
  ensures access c ** access c
{
  unfold access;
  with p. _;
  Lock.share c.lock;
  fold access c;
  fold access c;
}
instance send_access c : is_send (access c) = FStar.Tactics.Typeclasses.solve

let rec accesses (cells:list cell) : Tot slprop (decreases cells) =
  match cells with
  | [] -> emp
  | c::cs -> access c ** accesses cs

let rec send_accesses (cells:list cell) : Tot (is_send (accesses cells)) (decreases cells) =
  match cells with
  | [] -> is_send_placeless emp
  | c::cs -> is_send_star (access c) (accesses cs) #(send_access c) #(send_accesses cs)
instance send_all cells : is_send (accesses cells) = send_accesses cells

ghost fn rec dup_accesses (cells:list cell) ()
  requires accesses cells
  ensures accesses cells ** accesses cells
  decreases cells
{
  unfold accesses cells;
  match cells {
    [] -> { fold accesses cells; fold accesses cells; }
    c::cs -> {
      dup_access c ();
      dup_accesses cs ();
      fold accesses cells;
      fold accesses cells;
    }
  }
}
instance duplicable_accesses cells : duplicable (accesses cells) = { dup_f = dup_accesses cells }

(** The authoritative half of every slot's shadow, including inactive slots. *)
let rec shadows (cells:list cell) (start:nat) (f:nat -> GTot nat)
  : Tot slprop (decreases cells) =
  match cells with
  | [] -> emp
  | c::cs -> G.pts_to c.shadow #0.5R (f start) ** shadows cs (start + 1) f

let rec placeless_shadows (cells:list cell) start f
  : Tot (placeless (shadows cells start f)) (decreases cells) =
  match cells with
  | [] -> placeless_emp
  | c::cs -> placeless_star _ _ #(G.pts_to_placeless c.shadow 0.5R (f start))
      #(placeless_shadows cs (start + 1) f)
instance shadows_placeless cells start f : placeless (shadows cells start f) =
  placeless_shadows cells start f

(** Borrow one fractional handle without disturbing the other slots. *)
ghost fn rec borrow (cells:list cell) (k:nat { k < L.length cells })
  preserves accesses cells
  ensures access (at cells k)
  decreases cells
{
  unfold accesses cells;
  match cells {
    c::cs -> {
      if (k = 0) {
        dup_access c ();
        rewrite access c as access (at cells k);
      } else {
        borrow cs (k - 1);
        rewrite access (at cs (k - 1)) as access (at cells k);
      };
      fold accesses cells;
    }
  }
}

(** Return a borrowed handle, preserving all physical ownership. *)
ghost fn rec give_back (cells:list cell) (k:nat { k < L.length cells })
  preserves accesses cells
  requires access (at cells k)
  decreases cells
{
  unfold accesses cells;
  match cells {
    c::cs -> {
      if (k = 0) {
        rewrite access (at cells k) as access c;
        unfold access c;
        with p. _;
        unfold access c;
        with q. _;
        Lock.gather c.lock;
        fold access c;
      } else {
        rewrite access (at cells k) as access (at cs (k - 1));
        give_back cs (k - 1);
      };
      fold accesses cells;
    }
  }
}

(** Relate a lock holder's shadow to the authoritative registry. *)
ghost fn rec agree (cells:list cell) (start:nat) (f:nat -> GTot nat)
  (k:nat { k < L.length cells }) (v:nat)
  preserves shadows cells start f ** G.pts_to (at cells k).shadow #0.5R v
  ensures pure (v == f (start + k))
  decreases cells
{
  unfold shadows cells start f;
  match cells {
    c::cs -> {
      if (k = 0) {
        rewrite G.pts_to (at cells k).shadow #0.5R v as G.pts_to c.shadow #0.5R v;
        G.pts_to_injective_eq c.shadow;
        rewrite G.pts_to c.shadow #0.5R v as G.pts_to (at cells k).shadow #0.5R v;
      } else {
        rewrite G.pts_to (at cells k).shadow #0.5R v
          as G.pts_to (at cs (k - 1)).shadow #0.5R v;
        agree cs (start + 1) f (k - 1) v;
        rewrite G.pts_to (at cs (k - 1)).shadow #0.5R v
          as G.pts_to (at cells k).shadow #0.5R v;
      };
      fold shadows cells start f;
    }
  }
}

(** Pointwise equality suffices to transport a registry's specification. *)
ghost fn rec shadows_ext (cells:list cell) (start:nat) (f g:nat -> GTot nat)
  requires shadows cells start f **
    pure (forall (j:nat). start <= j /\ j < start + L.length cells ==> f j == g j)
  ensures shadows cells start g
  decreases cells
{
  unfold shadows cells start f;
  match cells {
    [] -> { fold shadows cells start g; }
    c::cs -> {
      rewrite G.pts_to c.shadow #0.5R (f start) as G.pts_to c.shadow #0.5R (g start);
      shadows_ext cs (start + 1) f g;
      fold shadows cells start g;
    }
  }
}

(** Change one shadow only when both agreeing halves are available. *)
ghost fn rec set_shadow (cells:list cell) (start:nat) (f:nat -> GTot nat)
  (k:nat { k < L.length cells }) (old value:nat)
  requires shadows cells start f ** G.pts_to (at cells k).shadow #0.5R old
  ensures shadows cells start (fun j -> if j == start + k then value else f j) **
    G.pts_to (at cells k).shadow #0.5R value
  decreases cells
{
  unfold shadows cells start f;
  match cells {
    c::cs -> {
      if (k = 0) {
        rewrite G.pts_to (at cells k).shadow #0.5R old as G.pts_to c.shadow #0.5R old;
        G.gather c.shadow;
        G.write c.shadow value;
        G.share c.shadow;
        rewrite each (1.0R /. 2.0R) as 0.5R;
        shadows_ext cs (start + 1) f (fun j -> if j == start + k then value else f j);
        rewrite G.pts_to c.shadow #0.5R value
          as G.pts_to (at cells k).shadow #0.5R value;
      } else {
        rewrite G.pts_to (at cells k).shadow #0.5R old
          as G.pts_to (at cs (k - 1)).shadow #0.5R old;
        set_shadow cs (start + 1) f (k - 1) old value;
        shadows_ext cs (start + 1)
          (fun j -> if j == start + 1 + (k - 1) then value else f j)
          (fun j -> if j == start + k then value else f j);
        rewrite G.pts_to (at cs (k - 1)).shadow #0.5R value
          as G.pts_to (at cells k).shadow #0.5R value;
      };
      fold shadows cells start (fun j -> if j == start + k then value else f j);
    }
  }
}

(** Allocate every node once; removal makes its slot available for reuse.
All locks are initially unlocked, and all ownership remains in the registry. *)
fn rec allocate (count start:nat) (initial:nat -> nat)
  returns cells:list cell
  ensures pure (L.length cells == count) **
    accesses cells ** shadows cells start initial
  decreases count
{
  if (count = 0) {
    fold accesses [];
    fold shadows [] start initial;
    []
  } else {
    let value = initial start;
    let next = B.alloc value;
    let shadow = G.alloc #nat value;
    G.share shadow;
    fold protected next shadow;
    let lock = Lock.new_lock (protected next shadow);
    let c = { next; shadow; lock };
    rewrite each next as c.next;
    rewrite each shadow as c.shadow;
    rewrite each lock as c.lock;
    fold access c;
    let cs = allocate (count - 1) (start + 1) initial;
    fold accesses (c::cs);
    fold shadows (c::cs) start initial;
    c::cs
  }
}

(** Locked physical edge and matching ghost half, with its borrowed handle. *)
let held (c:cell) (v:nat) =
  access c ** Lock.lock_acquired c.lock **
  B.pts_to c.next v ** G.pts_to c.shadow #0.5R v

divergent fn acquire (cells:list cell) (k:nat { k < L.length cells })
  preserves accesses cells
  returns v:nat
  ensures held (at cells k) v
{
  borrow cells k;
  let c = at cells k;
  rewrite access (at cells k) as access c;
  unfold access c;
  with p. _;
  Lock.acquire c.lock;
  unfold protected;
  with old. _;
  let v = B.(!c.next);
  fold access c;
  fold held c v;
  rewrite held c v as held (at cells k) v;
  v
}

fn release (cells:list cell) (k:nat { k < L.length cells }) (#v:erased nat)
  preserves accesses cells
  requires held (at cells k) v
{
  let c = at cells k;
  rewrite held (at cells k) v as held c v;
  unfold held c v;
  unfold access c;
  with p. _;
  fold protected c.next c.shadow;
  Lock.release c.lock;
  fold access c;
  rewrite access c as access (at cells k);
  give_back cells k;
}
