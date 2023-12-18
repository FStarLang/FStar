module BugWhileInv
open Pulse.Lib.Pervasives

let workaround (b:bool) (v:nat) : vprop =
    pure (not b ==> v == 0)

```pulse
fn count_down_ugly (x:ref nat)
requires exists* v. pts_to x v
ensures pts_to x 0
{
  with v. assert (pts_to x v);
  fold (workaround true v);
  while (
    let v = !x;
    with b v'. unfold (workaround b v');
    if (v = 0)
    {
      fold (workaround false v);
      false;
    }
    else
    {
      x := v - 1;
      fold (workaround true (v - 1));
      true;
    }
  )
  invariant b.
    exists* v. 
        pts_to x v **
        workaround b v
  { () };
  with v. unfold (workaround false v);
 }
```

```pulse
fn count_down (x:ref nat)
requires exists* v. pts_to x v
ensures pts_to x 0
{
  while (
    let v = !x;
    if (v = 0)
    {
      false;
    }
    else
    {
      x := v - 1;
      true;
    }
  )
  invariant b.
    exists* v. 
        pts_to x v **
        pure ((b == false) ==> (v == 0))
  { () };
 }
```