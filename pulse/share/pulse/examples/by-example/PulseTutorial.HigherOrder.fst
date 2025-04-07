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

module PulseTutorial.HigherOrder
#lang-pulse
open Pulse.Lib.Pervasives

//apply$
fn apply (#a:Type0)
         (#b:a -> Type0)
         (#pre:a -> slprop)
         (#post: (x:a -> b x -> slprop))
         (f: (x:a -> stt (b x) (pre x) (fun y -> post x y)))
         (x:a)
requires pre x
returns y:b x
ensures post x y
{
  f x
}
//end apply$


//apply_ghost$
ghost
fn apply_ghost 
         (#a:Type0)
         (#b:a -> Type0)
         (#pre:a -> slprop)
         (#post: (x:a -> b x -> slprop))
         (f: (x:a -> stt_ghost (b x) emp_inames (pre x) (fun y -> post x y)))
         (x:a)
requires pre x
returns y:b x
ensures post x y
{
  f x
}
//end apply_ghost$


let id_t = (#a:Type0) -> x:a -> stt a emp (fun _ -> emp)

fn id ()
: id_t 
= (#a:Type0) (x:a) { x }

let id_t_a (a:Type0) = x:a -> stt a emp (fun _ -> emp)

fn id_a (a:Type0)
: id_t_a a 
= (x:a) { x }


//ctr$
noeq
type ctr = {
    inv: int -> slprop;
    next: i:erased int -> stt int (inv i) (fun y -> inv (i + 1) ** pure (y == reveal i));
    destroy: i:erased int -> stt unit (inv i) (fun _ -> emp)
}
//end ctr$
let next c = c.next
let destroy c = c.destroy

//new_counter$
fn new_counter ()
requires emp
returns c:ctr
ensures c.inv 0
{
    open Pulse.Lib.Box;
    let x = alloc 0;
    fn next (i:erased int)
    requires pts_to x i 
    returns j:int
    ensures pts_to x (i + 1) ** pure (j == reveal i)
    {
        let j = !x;
        x := j + 1;
        j
    };
    fn destroy (i:erased int)
    requires pts_to x i
    ensures emp
    {
       free x
    };
    let c = { inv = pts_to x; next; destroy };
    rewrite (pts_to x 0) as (c.inv 0);
    c
}
//end new_counter$

fn return (#a:Type0) (x:a)
requires emp
returns y:a
ensures pure (x == y)
{
    x
}



//test_counter$
fn test_counter ()
requires emp
ensures emp
{
    let c = new_counter ();
    let next = c.next;
    let destroy = c.destroy;
    let x = next _; //FIXME: Should be able to write c.next
    assert pure (x == 0);
    let x = next _;
    assert pure (x == 1);
    destroy _;
}
//end test_counter$