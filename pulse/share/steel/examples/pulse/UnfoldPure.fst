module UnfoldPure
open Pulse.Lib.Pervasives
module US = FStar.SizeT

//Some examples illustrating how Pulse eliminates pure predicates
//automatically, but requires vprops to be explicitly unfolded

let pre0 (x:nat) : prop = x > 2
let pre1 (x:nat) : prop = pre0 x (* unnecessarily-nested props to test this *)

```pulse
fn unfold_pure1 (#x:nat)
  requires pure (pre1 x)
  ensures pure (x > 1)
{
  //Pulse eliminates `pure (pre1 x)` automatically
  //and types the continuation in the context with  ..., _:squash (pre1 x) |- ...
  //enabling the use of that hypothesis in queries to the SMT solver
  ()
  //Pulse a introduces `pure` automatically, by calling the SMT solver to prove
  // x > 1 in the current context (which since it includes squash (pre1 x) is
  // sufficient to prove x > 2)
}
```


(* unfold necessary - pulse won't automatically unfold a vprop *)

let pre2 (x:nat) : vprop = pure (x > 2)

```pulse
fn unfold_pure2 (#x:nat)
  requires pre2 x
  ensures pure (x > 1)
{
  //However, if the pure vprop is "hidden" behind a definition
  //Pulse requires it to be explicitly unfolded first
  unfold (pre2 x);
  //now things work as in the previous example
  ()
}
```


(* Note, you can't call unfold/fold on `pure p` since `pure` is a primitive
  (Nor do you need to, since it's eliminated/introduced automatically).
  Pulse complains with the error message:
  fold` and `unfold` expect a single user-defined predicate as an argument, but pure (
        Prims.op_GreaterThan x 2) is a primitive term that cannot be folded or unfolded
*)
[@@expect_failure]
```pulse
fn unfold_pure3 (#x:nat)
  requires pure (x > 2)
  ensures pure (x > 1)
{
  unfold (pure (x > 2));
  ()
}
```