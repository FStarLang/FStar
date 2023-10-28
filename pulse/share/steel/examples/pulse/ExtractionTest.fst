module ExtractionTest
open Pulse.Lib.Pervasives
module U32 = FStar.UInt32
open FStar.UInt32
inline_for_extraction
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


[@@"inline"]
```pulse
fn test_write_10 (x:ref U32.t)
   requires pts_to x 'n
   ensures  pts_to x 0ul
{
    x := 2ul;
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

module SZ = FStar.SizeT
module A = Pulse.Lib.Array

```pulse
fn fill_array (x:array U32.t) (n:SZ.t) (v:U32.t)
  requires A.pts_to x 's ** pure (A.length x == SZ.v n)
  ensures exists s. A.pts_to x s ** pure (Seq.equal s (Seq.create (SZ.v n) v))
{
  A.pts_to_len x;
  let mut i : SZ.t = 0sz;
  while (SZ.(i `SZ.lt` n))
  invariant b.
    exists (vi:SZ.t) (s:Seq.seq U32.t).
      pts_to i vi **
      A.pts_to x s **
      pure (SZ.(vi <=^ n) /\
            Seq.length s == Seq.length 's /\
            (forall (j:nat). j < SZ.v vi ==> Seq.index s j == v) /\
            b == SZ.(vi <^ n))
  {
    x.(i) <- v;
    i := i `SZ.add` 1sz;
  }
}
```

```pulse
fn extract_match (x:option bool)
  requires emp
  returns b:bool
  ensures emp
{
  match x {
    None ->
    {
      false
    }
    Some b ->
    {
      not b
    }
  }
}
```