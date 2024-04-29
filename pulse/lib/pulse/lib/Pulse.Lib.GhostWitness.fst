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

module Pulse.Lib.GhostWitness

open Pulse.Lib.Pervasives

let sqeq (p : Type) (_ : squash p) : erased p =
  FStar.IndefiniteDescription.elim_squash #p ()

let psquash (a:Type u#a) : prop = squash a

```pulse
ghost
fn ghost_witness (a:Type u#0) (_:squash a)
requires emp
returns i:a
ensures emp
{
  let pf = elim_pure_explicit (psquash a);
  let pf : squash a = FStar.Squash.join_squash pf;
  let i = sqeq a pf;
  let i = reveal i;
  i
}
```

```pulse
ghost
fn ghost_witness2 (a:Type u#4) (_:squash a)
requires emp
returns i:a
ensures emp
{
  let pf = elim_pure_explicit (psquash a);
  let pf : squash a = FStar.Squash.join_squash pf;
  let i = sqeq a pf;
  let i = reveal i;
  i
}
```

```pulse
ghost
fn ghost_witness_exists (a:Type u#0)
requires pure (exists (x:a). True)
returns i:a
ensures emp
{
  ghost_witness a ();
}
```

```pulse
ghost
fn ghost_witness_exists2 (a:Type u#4)
requires pure (exists (x:a). True)
returns i:a
ensures emp
{
  ghost_witness2 a ();
}
```


// fails
// ```pulse
// fn ghost_witness_exists_star (a:Type u#0)
// requires exists* (x:a). emp
// returns xx:int
// ensures emp
// {
//   with i. _;
// }
// ```
