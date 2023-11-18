module Bug113

open Pulse.Lib.Core

assume
val p : nat -> vprop
assume
val f : (x:bool -> #index:nat -> stt bool (p index) (fun _ -> emp))

[@@ expect_failure]
```pulse
fn apply_with_imps_inst3 (x:bool) (#i:erased nat)
    requires p i
    returns b:bool
    ensures emp
{
    f x
}
```
