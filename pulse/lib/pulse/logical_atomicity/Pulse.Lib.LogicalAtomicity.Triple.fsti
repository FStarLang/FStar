module Pulse.Lib.LogicalAtomicity.Triple
#lang-pulse

(**
Client-side construction of a logically atomic specification.

The library operation consumes an AU for its alpha/beta transition. The
client keeps alpha inside an invariant, supplies any private `extra`
ownership, and provides ghost code to run at commitment. This constructor
connects those two views without exposing the implementation's linearization
point to the client or requiring a new triple syntax in the checker.

The ghost `finish` callback is related to HoCAP's client-supplied ghost-code
style of specification. Packaging it in an abortable, retryable AU gives the
Iris-style protocol used here. TaDA motivates the abstract atomic operation
view, but this module does not implement TaDA regions/guards or derive an
equivalence with HoCAP or TaDA's proof rules; see README.md for references.

This is one derived introduction rule, not a complete logic of atomic
triples: one client invariant, fixed opening cost one, an empty-footprint
ghost callback, and no general sendability or liveness rule.
*)

open Pulse.Lib.Pervasives
module A = Pulse.Lib.LogicalAtomicity.Atomic

(** Client invariant body: operation-visible alpha and client-private
residual at the SAME abstract state. Residual never escapes to the operation. *)
let payload (#a:Type0) (alpha residual:a -> slprop) =
  exists* x. alpha x ** residual x

(** Capture extra and the invariant handle as retry state. Each opening
spends one credit and exposes alpha. Abort reunites alpha with residual and
returns extra; commit calls finish with beta, residual, and extra, restores
the invariant (possibly at a new abstract state), and returns phi.

The caller supplies finish for EVERY x and y allowed by alpha/beta, not just
an expected call-entry state. Its empty footprint makes it safe while the
client invariant is open. Captured extra may be consumed only on commitment. *)
ghost fn from_invariant (#a #b:Type0)
  (outer:inames) (i:iname { not (mem_inv outer i) })
  (alpha residual:a -> slprop) (beta phi:a -> b -> slprop) (extra:slprop)
  (finish:(x:a -> y:b -> unit ->
    stt_ghost unit emp_inames (extra ** residual x ** beta x y)
      (fun _ -> payload alpha residual ** phi x y)))
  requires inv i (payload alpha residual) ** extra
  ensures A.atomic_update outer (add_inv outer i) 1 alpha beta phi
