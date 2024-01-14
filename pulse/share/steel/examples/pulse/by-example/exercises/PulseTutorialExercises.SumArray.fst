module PulseTutorialExercises.SumArray
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
module SZ = FStar.SizeT
open FStar.SizeT
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
    admit()
}
```
