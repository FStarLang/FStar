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

module BugUnificationUnderBinder
open Pulse.Lib.Pervasives

assume
val p (x:int) (y:int) : slprop

```pulse
fn test (_:unit)
requires exists* x. p x 5
ensures emp
{
    with zz. assert (exists* x. p x zz);
    drop_ _;
}
```

```pulse
fn test_fa (_:unit)
requires forall* x. p x 5
ensures emp
{
    with zz. assert (forall* x. p x zz);
    drop_ _;
} 
```

assume
val is_list (l:list int) : slprop
open FStar.List.Tot

let aux (l1 l2:list 'a) (x:'a) 
: Lemma 
    (ensures l1@(x::l2) == (l1 @ [x])@l2)
    [SMTPat (l1@(x::l2))]
= List.Tot.Properties.append_assoc l1 [x] l2

```pulse
fn test1 (pfx:list int) (hd:int)
requires forall* tl. is_list (pfx @ (hd::tl))
ensures emp
{
    rewrite (forall* tl. is_list (pfx @ (hd::tl)))
          as (forall* tl. is_list ((pfx @ [hd])@tl));
    admit()
}
```