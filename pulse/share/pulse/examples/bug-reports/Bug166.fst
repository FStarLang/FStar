module Bug166
open Pulse

inline_for_extraction noextract
```pulse
fn h ()
  requires emp
  returns  x : int
  ensures  emp
{
  42
}
```
let h2 = h