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

module PulseExample.UseBigRef
open Pulse.Lib.Pervasives
open Pulse.Lib.BigReference

module B = Pulse.Lib.BigReference
module L = Pulse.Lib.SpinLock

let thunk (p q : small_vprop) = unit -> stt unit (up p) (fun _ -> up q)
let closure = (p:small_vprop & q:small_vprop & thunk p q)
let closure_list = B.ref (list closure)
let vprop0 = v:vprop { is_small v }

```pulse
fn mk_closure_list ()
requires emp
returns r:closure_list
ensures B.pts_to r []
{
  B.alloc #(list closure) []
}
```

let mk_closure
    (#p #q:vprop0)
    (f: unit -> stt unit p (fun _ -> q))
: closure
= (| down p, down q, f |)


```pulse
fn push (l:closure_list)
        (#p #q:vprop0)
        (f: unit -> stt unit p (fun _ -> q))
requires B.pts_to l 'xs
ensures B.pts_to l (mk_closure f :: 'xs)
{
  open B;
  let xs = !l;
  l := (mk_closure f :: xs)
}
```

let pre_of (c:closure) =
  let (| p, _, _ |) = c in
  up p

let rec inv (l:list closure) =
  match l with
  | [] -> emp
  | hd :: tl -> pre_of hd ** inv tl

```pulse
ghost
fn intro_inv_nil (l:list closure)
requires pure (l == [])
ensures inv l
{
  fold (inv [])
}
```

```pulse
ghost
fn elim_inv_nil (l:list closure)
requires inv l ** pure (l == [])
ensures emp
{
  unfold (inv [])
}
```

```pulse
ghost
fn intro_inv_cons
        (l:list closure)
        (c:closure)
        (tl:list closure)
requires inv tl ** pre_of c ** pure (l == c :: tl)
ensures inv l
{
  fold (inv (c :: tl))
}
```

```pulse
ghost
fn elim_inv_cons
        (l:list closure)
        (c:closure)
        (tl:list closure)
requires inv l ** pure (l == c :: tl)
ensures pre_of c ** inv tl
{
  unfold (inv (c :: tl))
}
```

let lock_inv (r:closure_list) =
  exists* (l:list closure). 
    B.pts_to r l **
    inv l

noeq
type taskp = {
  task_list: closure_list;
  lock: Pulse.Lib.SpinLock.lock (lock_inv task_list)
}

```pulse
fn create_taskp ()
requires emp
returns t:taskp
ensures emp
{
  let task_list = mk_closure_list();
  intro_inv_nil [];
  fold (lock_inv task_list);
  let lock = L.new_lock (lock_inv task_list);
  let l : taskp = { task_list; lock };
  l
}
```

let post_of (c:closure) =
  let (| _, q, _ |) = c in
  up q

let run_thunk_of_closure (c:closure) 
: unit -> stt unit (pre_of c) (fun _ -> post_of c)
= let (| p, q, f |) = c in f

```pulse
fn run_closure (c:closure)
requires pre_of c
ensures emp
{
  run_thunk_of_closure c ();
  drop_ (post_of c)
}
```

```pulse
fn run_task (t:taskp)
requires emp
ensures emp
{
  open B;
  L.acquire t.lock;
  unfold (lock_inv t.task_list);
  let thunks = !t.task_list;
  match thunks {
    Nil -> {
      fold (lock_inv t.task_list);
      L.release t.lock;
    }
    Cons hd tl -> {
      elim_inv_cons thunks hd tl;
      t.task_list := tl;
      fold (lock_inv t.task_list);
      L.release t.lock;
      run_closure hd;
    }
  }
}
```
