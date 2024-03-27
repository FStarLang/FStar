module Bug13
open Pulse.Lib.Pervasives

let effectful_deghost #t (x:erased t) = stt t emp (fun y -> pure (reveal x == y))
let effectful_all_deghost (t: Type0) = x:erased t -> effectful_deghost #t x

[@@ expect_failure]  // TODO
```pulse
fn ead_unit () : effectful_all_deghost unit = x { () }
```
