module ExtractionTest
open Pulse.Lib.Pervasives
module U32 = FStar.UInt32
open FStar.UInt32
let zero () = 0ul


```pulse
fn test_read_write (x:ref U32.t)
  requires pts_to x 'n
  ensures pts_to x 'n
{
  let n = !x;
  x := n +^ (zero());
}
```

```pulse
fn test_write_10 (x:ref U32.t)
   requires pts_to x 'n
   ensures  pts_to x 0ul
{
    x := 1ul;
    test_read_write x;
    x := 0ul;
}
```

#push-options "--ext 'pulse:rvalues'"
```pulse
fn write10 (x:ref U32.t)
  requires pts_to x 'n
  ensures pts_to x 0ul
{
  let mut ctr = 10ul;
  while ((ctr >^ 0ul))
  invariant b.
    exists n i.
      pts_to x n **
      pts_to ctr i **
      pure (i <=^ 10ul /\ 
           (i <^ 10ul ==> n == 0ul) /\
           (b == (i >^ 0ul)))
  {
    test_write_10 x;
    ctr := ctr -^ 1ul;
  }
}
```
#pop-options
let test_write_10_pub x #n = write10 x
