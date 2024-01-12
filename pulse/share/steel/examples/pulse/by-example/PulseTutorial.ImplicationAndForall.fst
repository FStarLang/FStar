module PulseTutorial.ImplicationAndForall
open Pulse.Lib.Pervasives
open Pulse.Lib.Stick.Util
open Pulse.Lib.Forall.Util
module I = Pulse.Lib.Stick.Util
module GR = Pulse.Lib.GhostReference
open GR

//regain_half$
let regain_half #a (x:GR.ref a) (v:a) =
  pts_to x #one_half v @==> pts_to x v
//regain_half$


```pulse //intro_regain_half$
ghost 
fn intro_regain_half (x:GR.ref int)
requires pts_to x 'v
ensures pts_to x #one_half 'v ** regain_half x 'v
{
  ghost
  fn aux ()
  requires pts_to x #one_half 'v ** pts_to x #one_half 'v
  ensures pts_to x 'v
  {
    GR.gather x;
  };
  GR.share x;
  I.intro _ _ _ aux;
  fold regain_half;
}
```

```pulse //use_regain_half$
ghost
fn use_regain_half (x:GR.ref int)
requires pts_to x #one_half 'v ** regain_half x 'v
ensures pts_to x 'v
{
  unfold regain_half;
  I.elim _ _;
}
```

//regain_half_q$
let regain_half_q #a (x:GR.ref a) =
  forall* u. pts_to x #one_half u @==> pts_to x u 
//regain_half_q$


module FA = Pulse.Lib.Forall.Util

```pulse //intro_regain_half_q$
ghost 
fn intro_regain_half_q (x:GR.ref int)
requires pts_to x 'v
ensures pts_to x #one_half 'v ** regain_half_q x
{
  ghost
  fn aux1 (u:int)
  requires pts_to x #one_half 'v ** pts_to x #one_half u
  ensures pts_to x u
  {
    gather x;
  };
  GR.share x;
  FA.intro_forall_imp _ _ _ aux1;
  fold regain_half_q;
}
```

```pulse //use_regain_half_q$
ghost
fn use_regain_half_q (x:GR.ref int)
requires pts_to x #one_half 'u ** regain_half_q x
ensures pts_to x 'u
{
  unfold regain_half_q;
  FA.elim #_ #(fun u -> pts_to x #one_half u @==> pts_to x u) 'u;
  I.elim _ _;
}
```

//can_update$
let can_update (x:GR.ref int) = 
  forall* u v. pts_to x #one_half u @==>
               pts_to x v
//can_update$

```pulse //make_can_update$
ghost
fn make_can_update (x:GR.ref int)
requires pts_to x w
ensures pts_to x #one_half w ** can_update x
{
  ghost
  fn aux (u:int)
  requires pts_to x #one_half w
  ensures forall* v. pts_to x #one_half u @==> pts_to x v
  {
    ghost
    fn aux (v:int)
    requires pts_to x #one_half w ** pts_to x #one_half u
    ensures pts_to x v
    {
      gather x;
      x := v;
    };
    FA.intro_forall_imp _ _ _ aux;
  };
  share x;
  FA.intro _ aux;
  fold (can_update x);
}
```

```pulse //update$
ghost
fn update (x:GR.ref int) (k:int)
requires pts_to x #one_half 'u ** can_update x
ensures pts_to x #one_half k ** can_update x
{
  unfold can_update;
  FA.elim #_ #(fun u -> forall* v. pts_to x #one_half u @==> pts_to x v) 'u;
  FA.elim #_ #(fun v -> pts_to x #one_half 'u @==> pts_to x v) k;
  I.elim _ _;
  make_can_update x;
}
```


