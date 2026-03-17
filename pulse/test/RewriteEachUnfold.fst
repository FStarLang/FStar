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


(* These work since we apply the rewrites_to substitution
   on each side before rewriting. *)
fn test1 (x: ref int)
  preserves exists* (yy: int). (x |-> yy) ** pure (yy == 42)
{
  let y = !x;
  rewrite each y as 42;
}

fn test2 (x: ref (ref int))
  preserves exists* (yy: ref int) zz. (x |-> yy) ** (yy |-> zz) ** pure (zz == 42)
{
  let z = ! !x;
  rewrite each z as 42;
}
