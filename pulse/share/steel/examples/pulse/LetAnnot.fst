module LetAnnot

open Pulse.Lib.Pervasives

(* This module just contains some unit tests for annotations on letbindings. *)

```pulse
fn test1 (_:unit) requires emp returns _:unit ensures emp {
  let x : nat = 42;
  ()
}
```

[@@expect_failure]
```pulse
fn test2 (_:unit) requires emp returns _:unit ensures emp {
  let x : bool = 42;
  ()
}
```

[@@expect_failure]
```pulse
fn test3 (_:unit) requires emp returns _:unit ensures emp {
  let x : pos = -1;
  ()
}
```

```pulse
fn testmut1 (_:unit) requires emp returns _:unit ensures emp {
  let mut x : nat = 42;
  ()
}
```

[@@expect_failure]
```pulse
fn testmut2 (_:unit) requires emp returns _:unit ensures emp {
  let mut x : bool = 42;
  ()
}
```

[@@expect_failure]
```pulse
fn testmut3 (_:unit) requires emp returns _:unit ensures emp {
  let mut x : pos = -1;
  ()
}
```

```pulse
fn ret (#a:Type0) (x:a) requires emp returns x:a ensures emp {
  x
}
```

```pulse
fn testst1 (_:unit) requires emp returns _:unit ensures emp {
  let x : int = ret 42;
  (* NB: This will not work at any type other than int (currently).
  The annotation is not used for inference of stateful assignments,
  and for them the annotated type must syntactically match the
  computed one. *)
  ()
}
```

[@@expect_failure]
```pulse
fn testst2 (_:unit) requires emp returns _:unit ensures emp {
  let mut x : bool = 42;
  ()
}
```

[@@expect_failure]
```pulse
fn testst3 (_:unit) requires emp returns _:unit ensures emp {
  let mut x : pos = -1;
  ()
}
```
