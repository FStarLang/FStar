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

module ExistsWitness
#lang-pulse
open Pulse.Lib.Pervasives
module R = Pulse.Lib.Reference
//This example illustrates how to get your "hands" on an existential witness
//Using the `with ... assert` construct


fn get_witness (x:R.ref int) (#p:perm) (#y:Ghost.erased int)
requires pts_to x #p y
returns z:Ghost.erased int
ensures pts_to x #p y ** pure (y==z)
{   
    y
}


let assume_squash (p:prop) : squash p = assume p


fn sample (x:R.ref int)
requires exists* p y. pts_to x #p y
ensures exists* p y. pts_to x #p y ** pure (y == 17)
{
    let y' = get_witness x;
    assume_squash (y'==17);
    ()
}



fn sample_ (x:R.ref int) (#p:perm)
requires exists* y. pts_to x #p y
ensures exists* y. pts_to x #p y ** pure (y == 17)
{
    let y = get_witness x;
    assume_squash (y==17);
    ()
}



fn sample2 (x:R.ref int) (#p:perm)
requires exists* y. pts_to x #p y
ensures exists* y. pts_to x #p y ** pure (y == 17)
{
    with (y:erased _).
    assert (pts_to x #p y);
    assume_squash (y==17);
    ()
}


assume val drop (p:slprop) : stt unit p (fun _ -> emp)


fn sample3 (x0:R.ref int) (x1:R.ref bool) (#p0 #p1:perm)
requires exists* v0 v1. pts_to x0 #p0 v0 ** pts_to x1 #p1 v1
ensures emp
{
    
    with (v0 v1:erased _).
    assert (pts_to x0 #p0 v0 ** pts_to x1 #p1 v1);
    drop (pts_to x0 #p0 v0);
    drop (pts_to x1 #p1 v1)
}



fn sample4 (x0:R.ref int) (x1:R.ref bool) (#p0 #p1:perm)
requires exists* v0 v1. pts_to x0 #p0 v0 ** pts_to x1 #p1 v1
ensures emp
{
    
    with v0 v1.
    assert pts_to x0 #p0 v0 ** pts_to x1 #p1 v1;
    drop (pts_to x0 #p0 v0);
    drop (pts_to x1 #p1 v1)
}



fn sample5 (x0:R.ref int) (x1:R.ref bool) (#p0 #p1:perm)
requires exists* v0 v1. pts_to x0 #p0 v0 ** pts_to x1 #p1 v1
ensures emp
{
    
    with v0.
    assert pts_to x0 #p0 v0;
    with v1.
    assert pts_to x1 #p1 v1;
    drop (pts_to x0 #p0 v0);
    drop (pts_to x1 #p1 v1)
}



fn sample6 (x0:R.ref int) (x1:R.ref bool)
requires exists* p0 p1 v0 v1. pts_to x0 #p0 v0 ** pts_to x1 #p1 v1
ensures emp
{
    
    with p0 p1 v0 v1.
    assert pts_to x0 #p0 v0 ** pts_to x1 #p1 v1;
    drop (pts_to x0 #p0 v0);
    drop (pts_to x1 #p1 v1)
}


//Now instead of writing out the whole predicate, if there's a unique
//existential in the environment, you can just bind its witnesses as below

fn sample7 (x0:R.ref int) (x1:R.ref bool)
requires exists* p0 p1 v0 v1. pts_to x0 #p0 v0 ** pts_to x1 #p1 v1
ensures emp
{
    assert exists* p0 p1 v0 v1. pts_to x0 #p0 v0 ** pts_to x1 #p1 v1;
    with p0 p1 v0 v1. _;
    drop (pts_to x0 #p0 v0);
    drop (pts_to x1 #p1 v1)
}

