module Pulse.Lib.LogicalAtomicity.Example.CachedWaitFree.Atomics
#lang-pulse

(**
Sequentially consistent single-cell primitives. As in Pulse.Lib.Primitives,
as_atomic lifts the exclusively owned sequential model. The strong exchange
returns the old value: unlike cas_box, failure proves a mismatch.

The explicit OCaml externs must synchronize EACH primitive, not a complete
big-atomic operation. Mathematical naturals avoid counter wraparound.
*)

open Pulse.Lib.Pervasives
module B = Pulse.Lib.Box

[@@custard_extern "CachedWF_atomics.read"]
let read (#a:Type0) (r:B.box a) (#v:erased a) (#p:perm) =
  Pulse.Lib.Core.as_atomic _ _ ((let open B in ( ! )) r #v #p)

[@@custard_extern "CachedWF_atomics.write"]
let write (#a:Type0) (r:B.box a) (v:a) (#old:erased a) =
  Pulse.Lib.Core.as_atomic _ _ ((let open B in ( := )) r v #old)

private fn exchange_impl (r:B.box nat) (expected desired:nat) (#old:erased nat)
  requires B.pts_to r old
  returns seen:nat
  ensures B.pts_to r (if seen == expected then desired else seen) **
    pure (seen == reveal old)
{
  let seen = B.(!r);
  if (seen = expected) { B.(r := desired); };
  seen
}

[@@custard_extern "CachedWF_atomics.exchange"]
let exchange (r:B.box nat) (expected desired:nat) (#old:erased nat) =
  Pulse.Lib.Core.as_atomic _ _ (exchange_impl r expected desired #old)
