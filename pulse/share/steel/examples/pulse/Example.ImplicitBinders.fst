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

module Example.ImplicitBinders
open Pulse.Lib.Pervasives
module U32 = FStar.UInt32
#push-options "--using_facts_from '* -FStar.Tactics -FStar.Reflection'"



```pulse
fn swap (r1 r2:ref U32.t)
  requires 
      pts_to r1 'n1 **
      pts_to r2 'n2
  ensures
      pts_to r1 'n2 **
      pts_to r2 'n1
{
  let x = !r1;
  let y = !r2;
  r1 := y;
  r2 := x
}
```

```pulse
fn test_read (r:ref U32.t)
   requires pts_to r #p 'n
   returns x : U32.t
   ensures pts_to r #p x
{
  !r
}
```