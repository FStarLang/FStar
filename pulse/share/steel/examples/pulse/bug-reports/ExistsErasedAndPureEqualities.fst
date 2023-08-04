module ExistsErasedAndPureEqualities
open Pulse.Lib.Pervasives
module R = Pulse.Lib.Reference

assume
val some_pred (x:R.ref int) (v:int) : vprop

//Intro exists with an erased variable fails
[@@expect_failure]
```pulse
fn test1 (x:R.ref int) (#v:Ghost.erased int)
  requires some_pred x v
  ensures some_pred x v
{
    introduce exists (v_:erased int). (
        pure (v == v_)
    ) with _;
  
    ()
}
```

//Intro exists with an erased variable in an equality bound on the left,
//fails weirdly with an SMT failure, where it tries to prove earsed int == int
//and hide v == v
//Intro exists with an erased variable fails
[@@expect_failure]
```pulse
fn test2 (x:R.ref int) (#v:Ghost.erased int)
  requires some_pred x v
  ensures some_pred x v
{
    introduce exists (v_:erased int). (
        pure (v == v_)
    ) with _;
  
    ()
}
```

//If you don't use an erased variable, this works fine if the variable is on the left
```pulse
fn test3 (x:R.ref int) (#v:Ghost.erased int)
  requires some_pred x v
  ensures emp
{
    introduce exists (v_:int). (
        pure (v_ == v)
    ) with _;
  
    admit()
}
```

//but fails if the variable is on the right
[@@expect_failure]
```pulse
fn test4 (x:R.ref int) (#v:Ghost.erased int)
  requires some_pred x v
  ensures emp
{
    introduce exists (v_:int). (
        pure (v == v_)
    ) with _;
  
    admit()
}
```