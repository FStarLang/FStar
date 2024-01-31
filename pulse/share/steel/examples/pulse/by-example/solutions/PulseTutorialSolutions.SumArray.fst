module PulseTutorialSolutions.SumArray
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
module SZ = FStar.SizeT
module R = Pulse.Lib.Reference

let rec sum_spec (s:Seq.seq int) : Tot int (decreases Seq.length s) =
  if Seq.length s = 0
  then 0
  else let prefix = Seq.slice s 0 (Seq.length s - 1) in
       let last = Seq.index s (Seq.length s - 1) in
        sum_spec prefix + last

open Pulse.Lib.BoundedIntegers

```pulse
fn sum #p (#s:erased _) (arr:array int) (len:SZ.t { v len == Seq.length s })
  requires pts_to arr #p s
  returns res:int
  ensures pts_to arr #p s ** pure (res == sum_spec s)
{
  let mut i = 0sz;
  let mut res = 0;

  while (
    let vi = !i;
    (vi < len)
  )
  invariant b.
    pts_to arr #p s **
    (exists* vi vres. (
       R.pts_to i vi **
       R.pts_to res vres **
       pure (
         v vi <= v len /\
         vres == sum_spec (Seq.slice s 0 (v vi)) /\
         (b == (vi < len))
       )))
  {
    let vi = !i;
    let v = arr.(vi);
    let vres = !res;
    res := vres + v;
    i := vi + 1sz
  };
  
  let vres = !res;
  vres
}
```
