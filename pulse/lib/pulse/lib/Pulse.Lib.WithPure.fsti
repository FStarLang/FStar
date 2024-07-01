module Pulse.Lib.WithPure

open Pulse.Lib.Core
open Pulse.Main

val with_pure
  (p : prop)
  (v : squash p -> vprop)
: vprop

val size_small
  (p : prop)
  (v : squash p -> vprop)
: Lemma (requires forall s. is_small (v s))
        (ensures  is_small (with_pure p v))
        [SMTPat (is_small (with_pure p v))]

val size_boxable
  (p : prop)
  (v : squash p -> vprop)
: Lemma (requires forall s. is_big (v s))
        (ensures  is_big (with_pure p v))
        [SMTPat (is_big (with_pure p v))]

```pulse
ghost
val fn intro_with_pure
  (p : prop)
  (v : squash p -> vprop)
  (_ : squash p)
  requires pure p ** v ()
  ensures  with_pure p v
```

```pulse
ghost
val fn elim_with_pure
  (p : prop)
  (v : squash p -> vprop)
  requires with_pure p v
  returns  _ : squash p
  ensures  v ()
```