module Bug97

open Pulse.Lib.Pervasives

assume val p : x:int -> v1:int -> v2:int -> vprop

assume val f : x:int -> #v1:int -> #v2:int{v2 > v1} ->
                stt unit (p x v1 v2) (fun _ -> emp)

// This should work!
[@@expect_failure]
```pulse
fn test (_:unit)
  requires p 1 2 4
  ensures emp
  {
    f 1
  }
```
