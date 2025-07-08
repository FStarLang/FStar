module RewriteEachUnfold

#lang-pulse
open Pulse

assume val foo : slprop
assume val baz : slprop
unfold let bar = foo

fn test (_ : squash (foo == baz))
  requires bar
  ensures  baz
{
  rewrite each bar as baz;
  ()
}
