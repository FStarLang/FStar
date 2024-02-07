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

module PulseTutorial.Conditionals
open Pulse.Lib.Pervasives

//SNIPPET_START: max$
let max_spec x y = if x < y then y else x

```pulse
fn max #p #q (x y:ref int)
requires pts_to x #p 'vx ** pts_to y #q 'vy
returns n:int
ensures pts_to x #p 'vx ** pts_to y #q 'vy
        ** pure (n == max_spec 'vx 'vy)
{
    let vx = !x;
    let vy = !y;
    if (vx > vy)
    {
        vx
    }
    else
    {
        vy
    }
}
```
//SNIPPET_END: max$

[@@expect_failure]
```pulse //max_alt_fail$
fn max_alt #p #q (x y:ref int)
requires pts_to x #p 'vx ** pts_to y #q 'vy
returns n:int
ensures pts_to x #p 'vx ** pts_to y #q 'vy
        ** pure (n == max_spec 'vx 'vy)
{
    let mut result = 0;
    let vx = !x;
    let vy = !y;
    if (vx > vy)
    {
        result := vx;
    }
    else
    {
        result := vy;
    };
    !result;
}
```


```pulse //max_alt$
fn max_alt #p #q (x y:ref int)
requires pts_to x #p 'vx ** pts_to y #q 'vy
returns n:int
ensures pts_to x #p 'vx ** pts_to y #q 'vy
        ** pure (n == max_spec 'vx 'vy)
{
    let mut result = 0;
    let vx = !x;
    let vy = !y;
    if (vx > vy)
    ensures
     exists* r.
       pts_to x #p 'vx **
       pts_to y #q 'vy **
       pts_to result r **
       pure (r == max_spec 'vx 'vy)
    {
        result := vx;
    }
    else
    {
        result := vy;
    };
    !result;
}
```


module T = FStar.Tactics

//SNIPPET_START: nullable_ref$
let nullable_ref a = option (ref a)

let pts_to_or_null #a
        (x:nullable_ref a) 
        (#[default_arg (`full_perm)] p:perm) //implicit argument with a default
        (v:option a)
: vprop
= match x with
  | None -> pure (v == None)
  | Some x -> exists* w. pts_to x #p w ** pure (v == Some w)
//SNIPPET_END: nullable_ref$

```pulse //read_nullable$
fn read_nullable #a #p (r:nullable_ref a)
requires pts_to_or_null r #p 'v
returns o:option a
ensures pts_to_or_null r #p 'v
        ** pure ('v == o)
{
    match r {
     Some x -> {
        rewrite each r as (Some x);
        unfold (pts_to_or_null (Some x) #p 'v);
        let o = !x;
        fold (pts_to_or_null (Some x) #p 'v);
        rewrite each (Some x) as r;
        Some o
     }
     None -> {
        rewrite each r as None;
        unfold (pts_to_or_null None #p 'v);
        fold (pts_to_or_null None #p 'v);
        rewrite each (None #(ref a)) as r;
        None #a
     }
    }
}
```

//SNIPPET_START: pts_to_or_null_helpers$
```pulse
ghost
fn elim_pts_to_or_null_none #a #p (r:nullable_ref a)
requires pts_to_or_null r #p 'v ** pure (r == None)
ensures pts_to_or_null r #p 'v ** pure ('v == None)
{
    rewrite each r as None;
    unfold (pts_to_or_null None #p 'v);
    fold (pts_to_or_null None #p 'v);
    rewrite each (None #(ref a)) as r;
}
```

```pulse
ghost
fn intro_pts_to_or_null_none #a #p (r:nullable_ref a)
requires pure (r == None)
ensures pts_to_or_null r #p None
{
    fold (pts_to_or_null #a None #p None);
    rewrite each (None #(ref a)) as r;
}
```

```pulse
ghost
fn elim_pts_to_or_null_some #a #p (r:nullable_ref a) (x:ref a)
requires pts_to_or_null r #p 'v ** pure (r == Some x)
ensures exists* w. pts_to x #p w ** pure ('v == Some w)
{
    rewrite each r as (Some x);
    unfold (pts_to_or_null (Some x) #p 'v);
}
```

```pulse
ghost
fn intro_pts_to_or_null_some #a #p (r:nullable_ref a) (x:ref a)
requires pts_to x #p 'v ** pure (r == Some x)
ensures pts_to_or_null r #p (Some 'v)
{
    fold (pts_to_or_null (Some x) #p (Some 'v));
    rewrite each (Some x) as r;
}
```
//SNIPPET_END: pts_to_or_null_helpers$

```pulse //read_nullable_alt$
fn read_nullable_alt #a #p (r:nullable_ref a)
requires pts_to_or_null r #p 'v
returns o:option a
ensures pts_to_or_null r #p 'v
        ** pure ('v == o)
{
    match r {
     Some x -> {
        elim_pts_to_or_null_some r x;
        let o = !x;
        intro_pts_to_or_null_some r x;
        Some o
     }
     None -> {
        elim_pts_to_or_null_none r;
        None #a
     }
    }
}
```

//SNIPPET_START: read_nullable_alt_fail$
[@@expect_failure]
```pulse
fn read_nullable_alt #a #p (r:nullable_ref a)
requires pts_to_or_null r #p 'v
returns o:option a
ensures emp
{
    match r {
     Some x -> { admit () }
     _ -> { 
        // we only have `r == _` in scope
        // not the negation of the prior branch conditions
        // i.e., unlike F*, we don't have not (Some? r)
        // so the assertion below fails
        assert (pure (r == None)); 
        admit() }
    }
}
```
//SNIPPET_END: read_nullable_alt_fail$

```pulse //write_nullable$
fn write_nullable #a (r:nullable_ref a) (v:a)
requires pts_to_or_null r 'v
ensures exists* w. pts_to_or_null r w ** pure (Some? r ==> w == Some v)
{
    match r {
     None -> { () }
     Some x -> {
        elim_pts_to_or_null_some r x;
        x := v;
        intro_pts_to_or_null_some r x;
     }
    }
}
```
