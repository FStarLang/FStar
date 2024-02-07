module BugGhostReturn
open Pulse.Lib.Pervasives

assume
val p (#a:Type) (x:a) : prop

assume
val some_lemma (#a:Type) (x:a)
  : Lemma (p x)

```pulse
fn use_some_lemma (#a:Type u#0) (x:a)
requires emp
ensures pure (p x)
{
  some_lemma x;
  ()
}
```

```pulse
ghost
fn use_some_lemma_ghost (#a:Type u#0) (x:a)
requires emp
ensures pure (p x)
{
  some_lemma x;
  ()
}
```