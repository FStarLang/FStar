module BugGhostReturn
#lang-pulse
open Pulse.Lib.Pervasives

assume
val p (#a:Type) (x:a) : prop

assume
val some_lemma (#a:Type) (x:a)
  : Lemma (p x)


fn use_some_lemma (#a:Type u#0) (x:a)
requires emp
ensures pure (p x)
{
  some_lemma x;
  ()
}



ghost
fn use_some_lemma_ghost (#a:Type u#0) (x:a)
requires emp
ensures pure (p x)
{
  some_lemma x;
  ()
}
