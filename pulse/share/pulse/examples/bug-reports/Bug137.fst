(*
   Copyright 2023 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module Bug137

open Pulse.Lib.Pervasives

```pulse
fn test_elim_pure (x:option bool)
requires exists* q. q ** pure (Some? x)
ensures exists* q. q ** pure (Some? x)
{
    let v = Some?.v x;
    ()
}
```

// This previously had an exists for p,q in the pre and post,
// but then that's very ambiguous. I think this captures the idea
// of the test anyway.
```pulse
fn test_elim_pure2 (x:option bool) (p q : vprop)
requires p ** (exists* r. r ** pure (Some? x)) ** q
ensures  p ** q ** (exists* r. r ** pure (Some? x))
{
    let v = Some?.v x;
    ()
}
```
