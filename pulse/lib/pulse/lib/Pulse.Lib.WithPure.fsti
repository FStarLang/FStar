module Pulse.Lib.WithPure

open Pulse.Lib.Core
open Pulse.Main

val with_pure
  (p : prop)
  (v : squash p -> slprop)
: slprop

val size_small
  (p : prop)
  (v : squash p -> slprop)
: Lemma (requires forall s. is_slprop2 (v s))
        (ensures  is_slprop2 (with_pure p v))
        [SMTPat (is_slprop2 (with_pure p v))]

val size_boxable
  (p : prop)
  (v : squash p -> slprop)
: Lemma (requires forall s. is_slprop3 (v s))
        (ensures  is_slprop3 (with_pure p v))
        [SMTPat (is_slprop3 (with_pure p v))]

```pulse
ghost
val fn intro_with_pure
  (p : prop)
  (v : squash p -> slprop)
  (_ : squash p)
  requires pure p ** v ()
  ensures  with_pure p v
```

```pulse
ghost
val fn elim_with_pure
  (p : prop)
  (v : squash p -> slprop)
  requires with_pure p v
  returns  _ : squash p
  ensures  v ()
```