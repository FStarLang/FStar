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

module Pulse.Lib.FlippableInv

open Pulse.Lib.Pervasives

val finv (p:slprop) : Type0

val off #p (fi : finv p) : slprop
val on  #p (fi : finv p) : slprop

val mk_finv (p:slprop { is_storable p }) : stt (finv p) emp (fun x -> off x)

val iname_of #p (f : finv p) : erased iname

```pulse
atomic
val fn flip_on (#p:slprop) (fi : finv p)
  requires off fi ** p
  ensures on fi
  opens [reveal (iname_of fi)]
  (* Why is reveal needed? *)
```

```pulse
atomic
val fn flip_off (#p:slprop) (fi : finv p)
  requires on fi
  ensures  off fi ** p
  opens [reveal (iname_of fi)]
  (* Why is reveal needed? *)
```
