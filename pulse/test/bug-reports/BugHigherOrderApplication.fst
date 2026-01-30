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

module BugHigherOrderApplication
#lang-pulse
open Pulse.Lib.Pervasives


fn apply (#a #b:Type0) (f: (x:a -> stt b emp (fun _ -> emp))) (x:a)
    requires emp
    returns y:b
    ensures emp
{
    f x
}



fn apply2 (#a #b:Type0) (f: (x:a -> stt b emp (fun _ -> emp))) (x:a)
    requires emp
    returns y:(b & b)
    ensures emp
{
    let fst = f x;
    let snd = f x;
    (fst, snd)
}



fn apply_with_imps (#a #b:Type0) (#p:(a -> slprop)) (#q:(a -> b -> slprop))
                  (f: (x:a -> stt b (p x) (fun y -> q x y)))
                  (x:a)
    requires p x
    returns y:b
    ensures q x y
{
    f x;
}



fn apply_with_imps_inst
    (#a #b:Type0) (#p:(a -> nat -> slprop)) (#q:(a -> nat -> b -> slprop))
    (f: (x:a -> #index:nat -> stt b (p x index) (fun y -> q x index y)))
    (x:a)
  requires p x 0
  returns y:b
  ensures q x 0 y
{
    f x;
}





fn apply_with_imps_explicit 
    (#a #b:Type0) (#p:(a -> nat -> slprop)) (#q:(a -> nat -> b -> slprop))
    (f: (x:a -> #index:erased nat -> stt b (p x index) (fun y -> q x index y)))
    (x:a) (#i:erased nat)
  requires p x i
  returns y:b
  ensures q x i y
{
    f x #i;
}



fn rec loop (x:int)
    requires emp
    returns y:int
    ensures emp
{
    let res = loop x;
    (res + 1)
}



fn curry_stt
    (#a #b #c:Type0)
    (f: (a -> stt (b -> (stt c emp (fun _ -> emp))) emp (fun _ -> emp)))
    (x:a) (y:b)
  requires emp
  returns _:c
  ensures emp
{
    let g = f x;
    g y
}


let id_t (a:Type) = a -> stt a emp (fun _ -> emp)


fn apply_id_t (f:id_t bool) (x:bool)
  requires emp
  returns _:bool
  ensures emp
{
   f x;
}


//binary
let choice_t (a:Type) = a -> a -> stt a emp (fun _ -> emp)


fn apply_choice (f:choice_t bool) (x y:bool)
  requires emp
  returns _:bool
  ensures emp
{
   f x y;
}


//with non-trivial pre / post

//binary
let swap_fun a = x:ref a -> y:ref a -> #vx:erased a -> #vy:erased a -> stt unit
    (requires pts_to x vx ** pts_to y vy)
    (ensures fun _ -> pts_to x vy ** pts_to y vx)


fn apply_swap2 (f:swap_fun int) (x y:ref int)
  requires pts_to x 'vx
  requires pts_to y 'vy
  ensures pts_to x 'vx
  ensures pts_to y 'vy
{
   f x y;
   f x y
}



noeq
type record = {
    first:bool;
    second: (bool -> stt bool emp (fun _ -> emp));
}


fn projection (r:record)
requires emp
returns _:bool
ensures emp
{
    let res = r.first;
    res
}



fn return (#a:Type0) (x:a)
requires emp
returns y:a
ensures pure (x == y)
{
    x
}



fn project_and_apply (r:record)
requires emp
returns _:bool
ensures emp
{
    let f = return r.second; //need the return since otherwise Pulse adds an equality refinement to the type of x
    f r.first
}


assume val g :  (f:(bool -> stt bool emp (fun _ -> emp)){ f == f })

fn apply_refined_function (b:bool)
requires emp
returns b:bool
ensures emp
{
    g b
}

