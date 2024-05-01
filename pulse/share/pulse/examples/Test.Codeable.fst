module Test.Codeable

open Pulse.Lib.Pervasives
open Pulse.Lib.Codeable

instance small_pts_to (#a:Type) (r : ref a) (p:perm) (v : a)
  : Pulse.Class.Small.small (pts_to r #p v)
  = Pulse.Class.Small.small_from_small_ref _ _

let test0 : small_code.t = encode emp
let test1 (r : ref int) : small_code.t = encode (pts_to r 0)
let test2 (r s : ref int) : small_code.t = encode (pts_to r 0 ** emp ** pts_to s 1)
