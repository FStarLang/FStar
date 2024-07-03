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

module Test.Basic2

open Pulse.Lib.Pervasives

// #set-options "--debug ggg"
// #set-options "--debug pulse,prover,ggg --print_full_names --print_implicits"

open Pulse.Lib.Stick.Util

```pulse
ghost
fn test_trans (p q r:slprop)
requires (p @==> q) ** (q @==> r)
ensures  (p @==> r)
{
    trans p _ r;
}
```
