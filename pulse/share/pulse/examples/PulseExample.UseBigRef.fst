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
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.BigReference

module B = Pulse.Lib.BigReference
module L = Pulse.Lib.SpinLock
(*
let thunk (p q : slprop2_base) = unit -> stt unit (up2 p) (fun _ -> up2 q)
let closure = (p:slprop2_base & q:slprop2_base & thunk p q)
let closure_list = B.ref (list closure)


fn mk_closure_list ()
requires emp
returns r:closure_list
ensures pts_to r []
{
  B.alloc #(list closure) []
}


let mk_closure
    (#p #q:slprop2)
    (f: unit -> stt unit p (fun _ -> q))
: closure
= (| down2 p, down2 q, f |)



fn push (l:closure_list)
        (#p #q:slprop2)
        (f: unit -> stt unit p (fun _ -> q))
requires pts_to l 'xs
ensures pts_to l (mk_closure f :: 'xs)
{
  open B;
  let xs = !l;
  l := (mk_closure f :: xs)
}


let pre_of (c:closure) : slprop2 =
  let (| p, _, _ |) = c in
  up2_is_slprop2 p;
  up2 p

let rec inv (l:list closure) : v:slprop { is_slprop2 v } =
  match l with
  | [] -> emp
  | hd :: tl -> pre_of hd ** inv tl


ghost
fn intro_inv_nil (l:list closure)
requires pure (l == [])
ensures inv l
{
  fold (inv [])
}



ghost
fn elim_inv_nil (l:list closure)
requires inv l ** pure (l == [])
ensures emp
{
  unfold (inv [])
}



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


let lock_inv (r:closure_list) : v:slprop { is_slprop3 v } =
  exists* (l:list closure). 
    pts_to r l **
    inv l

noeq
type taskp = {
  task_list: closure_list;
  lock: Pulse.Lib.SpinLock.lock
}


fn create_taskp ()
requires emp
returns t:taskp
ensures L.lock_alive t.lock (lock_inv t.task_list)
{
  let task_list = mk_closure_list();
  intro_inv_nil [];
  fold (lock_inv task_list);
  let lock = L.new_lock (lock_inv task_list);
  let l : taskp = { task_list; lock };
  rewrite each task_list as l.task_list;
  rewrite each lock as l.lock;
  l
}


let post_of (c:closure) =
  let (| _, q, _ |) = c in
  up2 q

let run_thunk_of_closure (c:closure) 
: unit -> stt unit (pre_of c) (fun _ -> post_of c)
= let (| p, q, f |) = c in f


fn run_closure (c:closure)
requires pre_of c
ensures emp
{
  run_thunk_of_closure c ();
  drop_ (post_of c)
}



fn rec run_task (t:taskp)
requires L.lock_alive t.lock (lock_inv t.task_list)
ensures emp
{
  open B;
  L.acquire t.lock;
  unfold (lock_inv t.task_list);
  let thunks = !t.task_list;
  match thunks {
    [] -> {
      L.free t.lock;
      B.free t.task_list;
      elim_inv_nil thunks;
    }
    hd :: tl -> {
      elim_inv_cons thunks hd tl;
      t.task_list := tl;
      fold (lock_inv t.task_list);
      L.release t.lock;
      run_closure hd;
      run_task t
    }
  }
}

*)