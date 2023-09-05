module AuxPredicate
open Pulse.Lib.Pervasives
module R = Pulse.Lib.Reference

(* This example illustrates how to work with auxiliary predicates.
   The style is quite explicit, with folds and unfolds.
   It could be improved by automated support for foldig & unfolding
   in the prover *)

// Defining a vprop using F* syntax. We do not yet allow
// writing Pulse syntax for vprops in predicates 
let my_inv (b:bool) (r:R.ref int) : vprop
  = exists_ (fun v -> 
      R.pts_to r v ** 
      pure ( (v==0 \/ v == 1) /\ b == (v = 0) )
    )


```pulse
fn invar_introduces_ghost (r:R.ref int)
  requires R.pts_to r 0
  ensures R.pts_to r 1
{
  r := 0;

  fold (my_inv true r); //to prove the precondition of the while loop

  while 
   (  //unfold the predicate to expose its contents to the prover context
      with b. unfold (my_inv b r);
      let vr = !r;
      let res = (vr = 0);
      //show that the condition restores the invariant by explicitly folding it back
      fold (my_inv res r);
      res
   )
  invariant b. my_inv b r
  {
    // Same in the body;
    // unfold to expose it
    unfold (my_inv true r);
    r := 1;
    // fold it back to show its preserved
    fold (my_inv false r)
  };

  // unfold after the loop for the postcondition 
  unfold (my_inv false r)
}
```


[@@expect_failure]
```pulse
fn invar_introduces_orig (r:R.ref int)
  requires R.pts_to r 0
  ensures R.pts_to r 1
{
  r := 0;

  fold (my_inv true r);

  while (let vr = !r; //fails here, as expected; we have my_inv, not pts_to
         (vr = 0))
  invariant b. my_inv b r
  {
    r := 1;
  };

  ()   
}
```

// If you don't introduce the indirection of my_inv
// it just works without further ado
```pulse
fn invar_introduces_ghost_alt (r:R.ref int)
  requires R.pts_to r 0
  ensures R.pts_to r 1
{
  r := 0;

  while (let vr = !r; (vr = 0))
  invariant b. 
    exists v.
      R.pts_to r v **
      pure ( (v==0 \/ v == 1) /\ b == (v = 0) )
  {
    r := 1;
  }
}
```

// Some other examples

```pulse
fn exists_introduces_ghost (r:R.ref int)
  requires R.pts_to r 0
  ensures exists v. R.pts_to r v ** pure (v == 0 \/ v == 1)
{
  r := 0;

  fold (my_inv true r);

  introduce exists b. (my_inv b r) with _; 
  // once you hide the witness in the existential
  // you lose knowledge about it, i.e., we do not know that r = 0
  with b. unfold (my_inv b r)
}
```

```pulse
fn with_assert_OK (r:R.ref int)
  requires R.pts_to r 0
  ensures R.pts_to r 0
{
  r := 0;

  fold (my_inv true r);

  with b. assert (my_inv b r); // similar to above but we don't lose access
                               // to witness b=true because with...assert... 
                               // puts b=true into the typing context

  assert (my_inv true r);
  unfold (my_inv true r);
}
```