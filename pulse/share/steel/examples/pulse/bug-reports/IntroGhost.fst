module IntroGhost
module PM = Pulse.Main
open Steel.ST.Array
open Steel.FractionalPermission
open Steel.ST.Util
open FStar.Ghost
open Pulse.Steel.Wrapper
module R = Steel.ST.Reference

(* 
  invariant pattern makes the condition var b 
  a ghost var, making it impossible to infer the
  entry condition to the loop because the condition
  var outside the loop is not ghost
*)
let my_inv (b:bool) (r:R.ref int) : vprop
  = exists_ (fun v -> 
      R.pts_to r full_perm v `star` 
      pure ( b == (v = 0) )
    )

[@@expect_failure]
```pulse
fn invar_introduces_ghost (r:R.ref int)
  requires R.pts_to r full_perm 0
  ensures R.pts_to r full_perm 1
{
  r := 0;

  fold (my_inv true r);

  while (let vr = !r; (vr = 0))
  invariant b. my_inv b r  // FAILS: trying to prove: my_inv (reveal (hide true)) r
                           // but typing context has: my_inv true r
  {
    r := 1;
  };

  ()
}
```

(* 
  intro exists pattern exhibits the 
  same issue as the invariant pattern 
*)
[@@expect_failure]
```pulse
fn exists_introduces_ghost (r:R.ref int)
  requires R.pts_to r full_perm 0
  ensures R.pts_to r full_perm 0
{
  r := 0;

  fold (my_inv true r);

  introduce exists b. (my_inv b r) with _;  // FAILS: trying to prove: my_inv (reveal (hide true)) r
                                            // but typing context has: my_inv true r
  ()
}
```

(* 
  building on above example: providing a witness 
  helps but then we lose access to the witness
*)
[@@expect_failure]
```pulse
fn exists_with_witness_introduces_ghost (r:R.ref int)
  requires R.pts_to r full_perm 0
  ensures R.pts_to r full_perm 0
{
  r := 0;

  fold (my_inv true r);

  introduce exists b. (my_inv b r) with true; // this is OK but then we lose access
                                              // to witness b=true

  assert_ (my_inv true r); // FAILS
  unfold (my_inv true r);
  ()
}
```

(* 
  building on above example: this checks! 
  use the with...assert... pattern to maintain the witness 
*)
```pulse
fn with_assert_OK (r:R.ref int)
  requires R.pts_to r full_perm 0
  ensures R.pts_to r full_perm 0
{
  r := 0;

  fold (my_inv true r);

  with b. assert (my_inv b r); // similar to above but we don't lose access
                               // to witness b=true because with...assert... 
                               // puts b=true into the typing context

  assert_ (my_inv true r);
  unfold (my_inv true r);
  ()
}
```