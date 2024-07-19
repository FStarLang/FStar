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

module Example.Ghost
open Pulse.Lib.Pervasives

//calling a function declared in F* as ghost fails
[@@expect_failure]
```pulse
ghost
fn test_elim_false (a:Type0) (p:(a -> slprop))
    requires pure False
    returns x:a
    ensures p x
{
    elim_false a p;
}
```

```pulse
ghost
fn elim_false_alt (a:Type0) (p:(a -> slprop))
    requires pure False
    returns x:a
    ensures p x
{
    let x = FStar.Pervasives.false_elim #a ();
    rewrite emp as (p x);
    x
}
```


```pulse
ghost
fn test_elim_false_alt (a:Type0) (p:(a -> slprop))
    requires pure False
    returns x:a
    ensures p x
{
    elim_false_alt a p;
}
```

// You can return anything in Ghost, it doesn't have to be non-informative
```pulse
ghost
fn ret (#a:Type0) (x:a)
    requires emp
    returns y:a
    ensures emp
{
    x
}
```


//You can also return it as erased, though you don't have to
```pulse
ghost
fn ret2 (#a:Type0) (x:a)
    requires emp
    returns y:erased a
    ensures emp
{
    hide x
}
```

//Admit is overloaded to work in all the effects, include ghost
```pulse
ghost
fn use_admit (t:Type0) (p:slprop)
    requires emp
    returns x:t
    ensures p
{
    admit()
}
```

assume
val p : slprop
assume
val q : slprop
assume
val r : slprop

```pulse
ghost
fn p_q ()
requires p
ensures q
{
    admit()
}
```

```pulse
ghost
fn q_r ()
requires q
ensures r
{
    admit()
}
```

```pulse
ghost
fn p_r ()
requires p
ensures r
{
   p_q();
   q_r();
}
```

