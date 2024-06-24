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

module DependentTuples

open Pulse.Lib.Pervasives

//
// The locks are no longer indexed by vprops
// Would need another instance of this problem
//

let exists_n (r:ref nat) : vprop = exists* n. pts_to r n

assume val t (v:vprop) : Type0

type tup_t = r:ref nat & t (exists_n r)
let mk_tup r x : tup_t = (| r, x |)

assume
val global_tup : tup_t

assume val get_v #v (l:t v) : stt unit emp (fun _ -> v)

#set-options "--print_implicits"

```pulse
fn tuple ()
  requires emp
  ensures emp
{
  get_v global_tup._2;
  assert (exists_n global_tup._1);
  unfold exists_n global_tup._1;
   (* THIS NOW WORKS FINE *)
   // this unfold affects the type of the dependent
   // tuple, so we lost syntactic equality and the
   // following assertion fails
  assert ((exists* n. pts_to global_tup._1 n));
  admit()
}
```

// the same program with a record instead of a dependent tuple works

noeq
type rec_t = 
{ r:ref nat;
  lk:t (exists_n r); }

assume
val global_rec : rec_t

```pulse
fn record ()
  requires emp
  ensures emp
{
  get_v global_rec.lk;
  assert (exists_n global_rec.r);
  unfold exists_n global_rec.r;
  assert (exists* n. pts_to global_rec.r n);
  admit()
}
```
